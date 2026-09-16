// SPDX-License-Identifier: LGPL-3.0-or-later

//! The off-chain side of the dispute game: the true state hash at any step of a verification,
//! computed in batched passes, and the input of the step that settles a game.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Mutex},
};

use pofseed_flock_lift_evm::evm::{Abi, encode};
use revm::primitives::{B256, U256};

use crate::{
    deploy::step_calldata,
    machine::Machine,
    scenario::{CALLS, Scenario},
    trace::{Capture, Captured, context, run_call},
    vm::{ACCEPTED, Committed, Ctx, REJECTED, StepWitness, terminal},
};

/// A verification's trace, as far as it goes: its calls' contexts and step counts, and how it
/// ends.
pub struct Oracle {
    /// The proof bytes.
    pub proof: Vec<u8>,
    /// Contexts of the calls that ran.
    pub ctxs: Vec<Ctx>,
    /// Steps of each call that ran; a call that rejects counts up to its last step.
    pub steps: Vec<u64>,
    /// The terminal state the trace ends in.
    pub end: u64,
    codes: [Vec<u8>; 2],
}

impl Oracle {
    /// Runs the verification of `proof` once, counting steps.
    pub fn new(machine: &mut Machine, scenario: &Scenario, proof: Vec<u8>, stream_body: &Arc<Vec<Vec<B256>>>) -> Self {
        let codes = [machine.code(scenario.lift), machine.code(scenario.discharge)];
        let mut outputs: Vec<Vec<u8>> = Vec::new();
        let mut ctxs = Vec::new();
        let mut steps = Vec::new();
        let mut end = ACCEPTED;
        for call in 0..CALLS {
            let ctx = context(scenario, &proof, &outputs, call, stream_body);
            let capture = Capture::new(BTreeSet::new(), None, Box::new(|_| {}));
            let unsupported = capture.unsupported.clone();
            let (ok, output, count) = run_call(machine, scenario, &ctx, capture);
            let first_unsupported = unsupported.lock().unwrap().iter().min().copied();
            ctxs.push(ctx);
            if let Some(k) = first_unsupported {
                steps.push(k + 1);
                end = REJECTED;
                break;
            }
            steps.push(count);
            if !ok {
                end = REJECTED;
                break;
            }
            if call == CALLS - 1 && !(output.len() == 32 && U256::from_be_slice(&output) == U256::from(1)) {
                end = REJECTED;
            }
            outputs.push(output);
        }
        return Self {
            proof,
            ctxs,
            steps,
            end,
            codes,
        };
    }

    /// Steps until the trace ends.
    pub fn len(&self) -> u64 {
        return self.steps.iter().sum();
    }

    /// Whether the trace is empty.
    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }

    /// Where global state `g` lies: `Some((call, step))`, or `None` past the end.
    pub fn locate(&self, g: u64) -> Option<(usize, u64)> {
        let mut at = g;
        for (call, &s) in self.steps.iter().enumerate() {
            if at < s {
                return Some((call, at));
            }
            at -= s;
        }
        return None;
    }

    fn code(&self, call: usize) -> Vec<u8> {
        return self.codes[if call == 0 { 0 } else { 1 }].clone();
    }

    /// The true state hashes at global states `gs`, one pass per call.
    pub fn hashes(&self, machine: &mut Machine, scenario: &Scenario, gs: &BTreeSet<u64>) -> BTreeMap<u64, B256> {
        let mut out = BTreeMap::new();
        let mut per_call: Vec<BTreeMap<u64, u64>> = vec![BTreeMap::new(); self.ctxs.len()];
        for &g in gs {
            match self.locate(g) {
                Some((call, k)) => {
                    per_call[call].insert(k, g);
                }
                None => {
                    out.insert(g, terminal(self.end));
                }
            }
        }
        for (call, wanted) in per_call.into_iter().enumerate() {
            if wanted.is_empty() {
                continue;
            }
            let found: Arc<Mutex<BTreeMap<u64, B256>>> = Arc::new(Mutex::new(BTreeMap::new()));
            let sink_found = found.clone();
            let ctx = self.ctxs[call].clone();
            let map = wanted.clone();
            let on = Box::new(move |cap: Captured| {
                let h = Committed::new(&cap.pre).hash(&ctx);
                sink_found.lock().unwrap().insert(map[&cap.step], h);
            });
            let capture = Capture::new(wanted.keys().copied().collect(), None, on);
            run_call(machine, scenario, &self.ctxs[call], capture);
            let found = std::mem::take(&mut *found.lock().unwrap());
            assert_eq!(found.len(), wanted.len(), "every wanted state of call {call} was reached");
            out.extend(found);
        }
        return out;
    }

    /// Calldata of `resolve` for each `(game, g)`, settling `game` by the step from global state
    /// `g`, with the witness's size; one pass per call.
    pub fn resolve_inputs(&self, machine: &mut Machine, scenario: &Scenario, wanted: &[(u64, u64)]) -> BTreeMap<u64, (Vec<u8>, usize)> {
        let mut out = BTreeMap::new();
        let mut per_call: Vec<BTreeMap<u64, Vec<u64>>> = vec![BTreeMap::new(); self.ctxs.len()];
        for &(game, g) in wanted {
            match self.locate(g) {
                Some((call, k)) => per_call[call].entry(k).or_default().push(game),
                None => {
                    out.insert(game, (terminal_resolve(game, self.end), 0));
                }
            }
        }
        for (call, targets) in per_call.into_iter().enumerate() {
            if targets.is_empty() {
                continue;
            }
            let found: Arc<Mutex<BTreeMap<u64, (Vec<u8>, usize)>>> = Arc::new(Mutex::new(BTreeMap::new()));
            let sink = found.clone();
            let ctx = self.ctxs[call].clone();
            let code = self.code(call);
            let map = targets.clone();
            let on = Box::new(move |cap: Captured| {
                let pre = Committed::new(&cap.pre);
                let (witness, _) = StepWitness::new(&pre, &ctx, &code).build();
                let step = step_calldata(&pre.pre(&ctx), &cap.pre, &ctx, &witness);
                for &game in &map[&cap.step] {
                    sink.lock().unwrap().insert(game, (resolve_calldata(game, &step), witness.words));
                }
            });
            run_call(machine, scenario, &self.ctxs[call], Capture::new(targets.keys().copied().collect(), None, on));
            out.extend(std::mem::take(&mut *found.lock().unwrap()));
        }
        return out;
    }
}

/// `resolve` calldata for `game` from the calldata of the matching `step` call.
pub fn resolve_calldata(game: u64, step: &[u8]) -> Vec<u8> {
    let mut data = Abi::call("resolve(uint256,uint256[5],uint256[],bytes,uint256[8],bytes)").0;
    data.extend_from_slice(&U256::from(game).to_be_bytes::<32>());
    let mut args = step[4..].to_vec();
    for slot in [5usize, 6, 15] {
        let at = 32 * slot;
        let off = U256::from_be_slice(&args[at..at + 32]) + U256::from(32);
        args[at..at + 32].copy_from_slice(&off.to_be_bytes::<32>());
    }
    data.extend_from_slice(&args);
    return data;
}

/// `resolve` calldata for `game` from a terminal state of kind `kind`.
pub fn terminal_resolve(game: u64, kind: u64) -> Vec<u8> {
    let step = encode("step(uint256[5],uint256[],bytes,uint256[8],bytes)", |a| {
        let mut a = a.uint(U256::from(kind));
        for _ in 0..4 {
            a = a.uint(U256::ZERO);
        }
        a = a.uints(&[]).bytes(&[]);
        for _ in 0..8 {
            a = a.uint(U256::ZERO);
        }
        a.bytes(&[0u8; 96])
    });
    return resolve_calldata(game, &step);
}
