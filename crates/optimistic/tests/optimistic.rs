// SPDX-License-Identifier: LGPL-3.0-or-later

//! The optimistic verification machinery on stand-in contracts: the dispute game with honest and
//! dishonest parties, the one-step contract against revm on random programs, and forged
//! witnesses.

use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

use pofseed_flock_lift_optimistic::{
    deploy::{deploy, step_calldata},
    fuzz,
    machine::Machine,
    merkle::{levels, words_of},
    scenario::Scenario,
    sim::simulate,
    trace::{Capture, Captured, context, run_call},
    vm::{BODY_DEPTH, Committed, StepWitness},
};

#[test]
fn every_game_ends_with_the_truthful_side_winning() {
    for arity in [2, 16] {
        let mut machine = Machine::new(false);
        let scenario = Scenario::mock(&mut machine);
        let mut tampered = scenario.proof.clone();
        tampered[0] = 0xff;
        let report = simulate(machine, &scenario, tampered, arity, false);
        assert_eq!(report.games.len(), 13);
        for g in &report.games {
            assert!(g.ok, "arity {arity}: {} ended with the wrong winner", g.name);
        }
        for (label, gas) in &report.gas {
            assert!(gas.iter().all(|&g| g <= 1 << 24), "{label} exceeds the transaction gas cap");
        }
    }
}

#[test]
fn the_one_step_contract_agrees_with_revm_on_random_programs() {
    let r = fuzz::run(300, 0x0dd_ba11, false);
    assert!(r.steps > 10_000 && r.rejecting > 100 && r.opcodes > 100, "the campaign exercised the machine: {r:?}");
    assert_eq!(r.mismatches, 0);
}

#[test]
fn forged_witnesses_are_refused() {
    let mut machine = Machine::new(false);
    let scenario = Scenario::mock(&mut machine);
    let body = Arc::new(levels(&words_of(&scenario.stream.segments[0]), BODY_DEPTH));
    let on = deploy(&mut machine, &scenario, body[BODY_DEPTH][0]);
    let ctx = context(&scenario, &scenario.proof, &[], 0, &body);
    let code = machine.code(scenario.lift);
    let calls: Arc<Mutex<Vec<(Vec<u8>, usize, usize)>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = calls.clone();
    let (c, k) = (ctx.clone(), code.clone());
    let on_capture = Box::new(move |cap: Captured| {
        let pre = Committed::new(&cap.pre);
        let (witness, _) = StepWitness::new(&pre, &c, &k).build();
        if witness.mem.is_empty() && witness.cd.is_empty() {
            return;
        }
        let data = step_calldata(&pre.pre(&c), &cap.pre, &c, &witness);
        let encoded = witness.encode().len();
        sink.lock().unwrap().push((data, encoded, witness.mem.len()));
    });
    run_call(&mut machine, &scenario, &ctx, Capture::new(BTreeSet::new(), Some(code.len()), on_capture));
    let calls = std::mem::take(&mut *calls.lock().unwrap());
    assert!(calls.len() > 20, "enough steps carry a witness");
    let mut forged = 0;
    for (data, encoded, mem_len) in calls {
        let good = machine.call(on.onestep, data.clone());
        assert!(good.success, "the genuine witness is accepted");
        let start = data.len() - encoded.div_ceil(32) * 32;
        let sections = [(start + 32, mem_len), (start + 64 + mem_len, encoded - 96 - mem_len)];
        for (at, len) in sections {
            if len < 96 {
                continue;
            }
            for offset in [96 + 31, len - 1] {
                let mut bad = data.clone();
                bad[at + offset] ^= 0x01;
                let out = machine.call(on.onestep, bad);
                let same = out.success && out.output == good.output;
                assert!(!same, "a forged witness byte changed nothing");
                forged += 1;
            }
        }
    }
    assert!(forged > 20, "enough forgeries were tried");
}
