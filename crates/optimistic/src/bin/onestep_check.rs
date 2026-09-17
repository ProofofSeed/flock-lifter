// SPDX-License-Identifier: LGPL-3.0-or-later

//! Checks the one-step contract against revm on real steps of a lift's verification: the first
//! step at every program counter of every call, every call-ending step, and random steps. For
//! each, the contract's hashes of the states before and after must equal those of the states
//! revm went through, and its gas is recorded.
//!
//! Usage: `onestep-check <responses> <lift-cache-file> [random-steps-per-call] [extra-steps]`,
//! where `extra-steps` is a comma-separated list of `call:step`.

use std::{
    collections::BTreeSet,
    env,
    sync::{Arc, Mutex},
    time::Instant,
};


use pofseed_flock_lift_optimistic::{
    deploy::{deploy, step_calldata},
    game::Oracle,
    machine::Machine,
    scenario::{CALLS, Scenario},
    trace::{Capture, Captured, Proofs, contexts, run_call},
    vm::{ACCEPTED, Committed, Ctx, REJECTED, StepWitness, start_hash, terminal},
};
use revm::primitives::{B256, U256};

struct Case {
    call: usize,
    step: u64,
    op: u8,
    calldata: Vec<u8>,
    before: B256,
    after: B256,
    words: usize,
}

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    return *seed;
}

fn main() {
    let n: usize = env::args().nth(1).map_or(219, |s| s.parse().expect("responses"));
    let cache = env::args().nth(2).expect("lift cache file");
    let randoms: usize = env::args().nth(3).map_or(200, |s| s.parse().expect("random steps"));
    let extra: Vec<(usize, u64)> = env::args()
        .nth(4)
        .map(|s| {
            s.split(',')
                .filter(|x| !x.is_empty())
                .map(|x| {
                    let (c, k) = x.split_once(':').expect("call:step");
                    (c.parse().unwrap(), k.parse().unwrap())
                })
                .collect()
        })
        .unwrap_or_default();
    let mut machine = Machine::new(false);
    let scenario = Scenario::new(&mut machine, n, &cache);
    let t = Instant::now();
    let plain = scenario.run(&mut machine);
    assert!(plain.success.iter().all(|&s| s), "the verification accepts");
    println!("plain run {:.1} s, gas {:?}", t.elapsed().as_secs_f64(), plain.gas);
    let proofs = Proofs {
        lift: scenario.proof.clone(),
        matrix: scenario.matrix_proof.clone(),
    };
    let counts = Oracle::new(&mut machine, &scenario, proofs.clone()).steps;
    println!("steps per call: {counts:?}");
    let ctxs = contexts(&scenario, &proofs, &plain.outputs[..1]);
    let on = deploy(&mut machine, &scenario);
    for (label, gas) in &on.gas {
        println!("deploy {label}: {gas} gas");
    }
    let codes = [machine.code(scenario.lift), machine.code(scenario.matrix)];
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut all_cases: Vec<Case> = Vec::new();
    let only: Option<Vec<usize>> = env::var("ONLY_CALLS").ok().map(|v| v.split(',').map(|c| c.parse().unwrap()).collect());
    for call in 0..CALLS {
        if only.as_ref().is_some_and(|o| !o.contains(&call)) {
            continue;
        }
        let ctx = ctxs[call].clone();
        let code = codes[call].clone();
        let next: Option<Ctx> = ctxs.get(call + 1).cloned();
        let cases: Arc<Mutex<Vec<Case>>> = Arc::new(Mutex::new(Vec::new()));
        let sink_cases = cases.clone();
        let ctx_c = ctx.clone();
        let code_c = code.clone();
        let on_capture = Box::new(move |cap: Captured| {
            let pre = Committed::new(&cap.pre);
            let (witness, output) = StepWitness::new(&pre, &ctx_c, &code_c).build();
            let op = code_c.get(cap.pre.pc).copied().unwrap_or(0);
            let after = match (&cap.post, &output) {
                (Some(post), None) => Committed::new(post).hash(&ctx_c),
                (None, Some(out)) => match &next {
                    Some(nc) => start_hash(nc),
                    None => terminal(if out.len() == 32 && U256::from_be_slice(out) == U256::from(1) { ACCEPTED } else { REJECTED }),
                },
                (None, None) => terminal(REJECTED),
                (Some(_), Some(_)) => panic!("a step both continued and ended the call"),
            };
            let calldata = step_calldata(&pre.pre(&ctx_c), &cap.pre, &ctx_c, &witness);
            sink_cases.lock().unwrap().push(Case {
                call: ctx_c.call,
                step: cap.step,
                op,
                calldata,
                before: pre.hash(&ctx_c),
                after,
                words: witness.words,
            });
        });
        let mut targets = BTreeSet::new();
        for &(c, k) in &extra {
            if c == call {
                targets.insert(k);
            }
        }
        let count = counts[call];
        for _ in 0..randoms {
            targets.insert(rng(&mut seed) % count);
        }
        targets.insert(count - 1);
        let t = Instant::now();
        let capture = Capture::new(targets, Some(code.len()), on_capture);
        let unsupported = capture.unsupported.clone();
        let (ok, output, steps) = run_call(&mut machine, &scenario, &ctx, capture);
        assert!(ok && output == plain.outputs[call], "traced call {call} reproduces the plain run");
        assert!(unsupported.lock().unwrap().is_empty(), "call {call} used an opcode outside the machine");
        let cases = std::mem::take(&mut *cases.lock().unwrap());
        println!("call {call}: {steps} steps, {} captured in {:.1} s", cases.len(), t.elapsed().as_secs_f64());
        all_cases.extend(cases);
    }
    let t = Instant::now();
    let mut failures = 0;
    let mut max_gas = (0u64, 0usize, 0u64, 0u8, 0usize);
    let mut by_op: Vec<(u64, u64)> = vec![(0, 0); 256];
    for case in &all_cases {
        let out = machine.call(on.onestep, case.calldata.clone());
        let good = out.success && out.output.len() == 64 && B256::from_slice(&out.output[..32]) == case.before && B256::from_slice(&out.output[32..]) == case.after;
        if !good {
            failures += 1;
            if failures <= 20 {
                let msg = if out.success { format!("hashes differ: before ok {}", B256::from_slice(&out.output[..32]) == case.before) } else { hex::encode(&out.output) };
                println!("MISMATCH call {} step {} op 0x{:02x}: {msg}", case.call, case.step, case.op);
            }
        }
        if out.gas > max_gas.0 {
            max_gas = (out.gas, case.call, case.step, case.op, case.words);
        }
        let e = &mut by_op[case.op as usize];
        e.0 += 1;
        e.1 = e.1.max(out.gas);
    }
    println!("checked {} steps in {:.1} s: {failures} mismatches", all_cases.len(), t.elapsed().as_secs_f64());
    println!(
        "heaviest step: {} gas (call {}, step {}, op 0x{:02x}, {} words proved)",
        max_gas.0, max_gas.1, max_gas.2, max_gas.3, max_gas.4
    );
    println!("per opcode (steps checked, most gas):");
    for (op, (count, gas)) in by_op.iter().enumerate() {
        if *count > 0 {
            println!("  0x{op:02x}: {count} steps, max {gas} gas");
        }
    }
    assert_eq!(failures, 0, "the one-step contract disagrees with revm");
}
