// SPDX-License-Identifier: LGPL-3.0-or-later

//! The verification as a trace of machine states: capturing states at chosen steps while revm
//! runs a call, and the calls' contexts from which state hashes and witnesses are built.

use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

use revm::{
    interpreter::{
        InstructionResult, Interpreter,
        interpreter::EthInterpreter,
        interpreter_types::{Jumps, LoopControl},
    },
    primitives::{B256, U256},
};

use crate::{
    machine::{Machine, Sink},
    scenario::{CALLS, Scenario, words_at},
    vm::{CallData, Ctx, MEM_DEPTH, Snap, supported},
};

/// Memory bytes the machine allows.
const MEM_LIMIT: usize = 32 << MEM_DEPTH;

/// Argument words before the body in call `call`'s calldata `data`.
pub fn prefix_words(call: usize, data: &[u8], outputs: &[Vec<u8>]) -> usize {
    let words = (data.len() - 4) / 32;
    return match call {
        0 => {
            let at = |i: usize| -> usize { u64::from_be_bytes(data[4 + 32 * i + 24..4 + 32 * i + 32].try_into().unwrap()) as usize };
            let proof_at = at(3);
            proof_at / 32 + 1
        }
        2 => {
            let n0 = words_at(&outputs[0], 32).len();
            let s = 2 * n0 / 112;
            4 + 1 + n0 + 1 + s + 1
        }
        _ => words,
    };
}

/// The context of call `call` of a verification whose earlier calls output `outputs`.
pub fn context(scenario: &Scenario, proof: &[u8], outputs: &[Vec<u8>], call: usize, stream_body: &Arc<Vec<Vec<B256>>>) -> Ctx {
    let data = scenario.calldata(call, outputs, proof);
    let p = prefix_words(call, &data, outputs);
    let body = if call == 2 { Some(stream_body.clone()) } else { None };
    return Ctx {
        call,
        calldata: CallData::new(data, p, body),
        outputs: outputs[..call].to_vec(),
    };
}

/// Contexts of every call of a verification that ran with `outputs`.
pub fn contexts(scenario: &Scenario, proof: &[u8], outputs: &[Vec<u8>], stream_body: &Arc<Vec<Vec<B256>>>) -> Vec<Ctx> {
    return (0..CALLS.min(outputs.len() + 1)).map(|call| context(scenario, proof, outputs, call, stream_body)).collect();
}

/// A step captured with the states before and after it.
pub struct Captured {
    /// Step index within the call.
    pub step: u64,
    /// The state before.
    pub pre: Snap,
    /// The state after, taken before the next step, if the step did not end the call.
    pub post: Option<Snap>,
}

/// What a capture does with a step, given the states before and after.
pub type OnCapture = Box<dyn FnMut(Captured) + Send>;

/// A sink capturing the steps it is told to, by index or by first sight of a program counter.
pub struct Capture {
    stop_after: Option<u64>,
    targets: Vec<u64>,
    next: usize,
    first_pcs: Option<Vec<bool>>,
    steps: u64,
    pending: Option<Captured>,
    on: OnCapture,
    /// Steps seen.
    pub total: Arc<Mutex<u64>>,
    /// Steps the machine rejects at although revm went on: an opcode outside the machine, a
    /// static call to anything but the SHA-256 precompile, or memory past its limit.
    pub unsupported: Arc<Mutex<Vec<u64>>>,
}

impl Capture {
    /// A sink capturing the steps `targets`, and the first step at each program counter if
    /// `first_pcs` is `Some(code_len)`.
    pub fn new(targets: BTreeSet<u64>, first_pcs: Option<usize>, on: OnCapture) -> Self {
        return Self {
            stop_after: None,
            targets: targets.into_iter().collect(),
            next: 0,
            first_pcs: first_pcs.map(|n| vec![false; n + 1]),
            steps: 0,
            pending: None,
            on,
            total: Arc::new(Mutex::new(0)),
            unsupported: Arc::new(Mutex::new(Vec::new())),
        };
    }
}

impl Capture {
    /// The same sink, halting the call once `steps` steps have run.
    pub fn stopping_after(mut self, steps: u64) -> Self {
        self.stop_after = Some(steps);
        return self;
    }
}

fn snap(interp: &Interpreter<EthInterpreter>) -> Snap {
    return Snap {
        pc: interp.bytecode.pc(),
        stack: interp.stack.data().to_vec(),
        memory: interp.memory.context_memory().to_vec(),
        ret: interp.return_data.0.to_vec(),
    };
}

impl Sink for Capture {
    fn step(&mut self, interp: &mut Interpreter<EthInterpreter>) {
        if let Some(mut done) = self.pending.take() {
            done.post = Some(snap(interp));
            (self.on)(done);
        }
        let k = self.steps;
        self.steps += 1;
        let op = interp.bytecode.opcode();
        let foreign_call = op == 0xfa && interp.stack.len() >= 6 && interp.stack.peek(1).is_ok_and(|a| a != U256::from(2));
        if !supported(op) || foreign_call {
            self.unsupported.lock().unwrap().push(k);
        }
        if k > 0 && interp.memory.len() > MEM_LIMIT {
            self.unsupported.lock().unwrap().push(k - 1);
        }
        let mut take = false;
        if self.next < self.targets.len() && self.targets[self.next] == k {
            self.next += 1;
            take = true;
        }
        if let Some(seen) = self.first_pcs.as_mut() {
            let pc = interp.bytecode.pc().min(seen.len() - 1);
            if !seen[pc] {
                seen[pc] = true;
                take = true;
            }
        }
        if take {
            self.pending = Some(Captured {
                step: k,
                pre: snap(interp),
                post: None,
            });
        }
    }

    fn step_end(&mut self, interp: &mut Interpreter<EthInterpreter>) {
        if self.stop_after.is_some_and(|n| self.steps > n) && interp.bytecode.is_not_end() {
            interp.halt(InstructionResult::Stop);
        }
    }

    fn into_any(mut self: Box<Self>) -> Box<dyn std::any::Any> {
        if let Some(done) = self.pending.take() {
            (self.on)(done);
        }
        *self.total.lock().unwrap() = self.steps;
        return self;
    }
}

/// Runs call `call` of the verification with `capture` observing it; returns the output and
/// whether it succeeded.
pub fn run_call(machine: &mut Machine, scenario: &Scenario, ctx: &Ctx, capture: Capture) -> (bool, Vec<u8>, u64) {
    let total = capture.total.clone();
    let (out, sink) = machine.call_traced(scenario.target(ctx.call), ctx.calldata.bytes.clone(), Some(Box::new(capture)));
    drop(sink.expect("sink").into_any());
    let steps = *total.lock().unwrap();
    return (out.success, out.output, steps);
}
