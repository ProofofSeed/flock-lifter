// SPDX-License-Identifier: LGPL-3.0-or-later

//! Plays the optimistic verification of a real lift end to end in revm: the proof's upload, an
//! unchallenged assertion confirmed after its window, and a set of disputed assertions in which
//! honest and dishonest asserters and challengers meet, every game played to its end. Every
//! transaction runs under mainnet's 2^24 gas cap and is metered, and each game's outcome is
//! checked against the side that told the truth.
//!
//! Usage: `dispute-sim <responses> <lift-cache-file> [arity]`.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    sync::Arc,
    time::Instant,
};

use pofseed_flock_lift_evm::evm::{artifact, encode};
use pofseed_flock_lift_optimistic::{
    deploy::deploy,
    game::Oracle,
    machine::{Machine, Outcome},
    merkle::{levels, words_of},
    scenario::{BINDING, Scenario},
    vm::{ACCEPTED, BODY_DEPTH, terminal},
};
use revm::primitives::{Address, B256, U256, keccak256};

const ASSERTER: Address = Address::new([0xa5; 20]);
const CHALLENGER: Address = Address::new([0xc4; 20]);
const DAY: u64 = 86_400;
const WINDOW: u64 = 7 * DAY;
const MOVE: u64 = DAY;
const CAP: u64 = 1 << 24;

fn ether(n: u64) -> U256 {
    return U256::from(n) * U256::from(10u64).pow(U256::from(18));
}

/// Which trace a party reports.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Proof {
    Valid,
    Tampered,
}

/// How the asserter reports states.
#[derive(Clone, Copy, Debug)]
enum Asserter {
    /// The truth.
    Honest,
    /// The truth before state `from`, invented states after it.
    LiesFrom(u64),
    /// Stops moving.
    Silent,
}

/// How the challenger picks sub-intervals.
#[derive(Clone, Copy, Debug)]
enum Challenger {
    /// The first sub-interval whose right end the asserter got wrong.
    Honest,
    /// Always the last sub-interval.
    Last,
    /// A pseudo-random sub-interval.
    Random,
    /// Stops moving.
    Silent,
}

struct Case {
    name: &'static str,
    proof: Proof,
    steps: u64,
    asserter: Asserter,
    challenger: Challenger,
    challenger_should_win: bool,
    resolver_is_asserter: bool,
    assertion: u64,
    game: u64,
    lo: u64,
    hi: u64,
    mids: Vec<B256>,
    turn: u8,
    done: bool,
    challenger_won: Option<bool>,
    rounds: usize,
    seed: u64,
}

struct Chain {
    machine: Machine,
    dispute: Address,
    gas: BTreeMap<String, Vec<u64>>,
    now: u64,
}

impl Chain {
    fn send(&mut self, label: &str, from: Address, data: Vec<u8>, value: U256) -> Outcome {
        let out = self.machine.call_as(from, self.dispute, data, value);
        assert!(out.gas <= CAP, "{label} exceeds the transaction gas cap");
        self.gas.entry(label.to_string()).or_default().push(out.gas);
        return out;
    }

    fn ok(&mut self, label: &str, from: Address, data: Vec<u8>, value: U256) -> Outcome {
        let out = self.send(label, from, data, value);
        assert!(out.success, "{label} failed: {}", hex::encode(&out.output));
        return out;
    }

    fn advance(&mut self, secs: u64) {
        self.now += secs;
        self.machine.set_time(self.now);
    }

    fn word(out: &Outcome, i: usize) -> U256 {
        return U256::from_be_slice(&out.output[32 * i..32 * i + 32]);
    }
}

fn points(lo: u64, hi: u64, arity: u64) -> Vec<u64> {
    let span = hi - lo;
    let k = span.min(arity);
    return (0..=k).map(|j| lo + ((span as u128 * j as u128) / k as u128) as u64).collect();
}

fn fake(g: u64) -> B256 {
    return keccak256([b"invented state".as_slice(), &g.to_be_bytes()].concat());
}

fn upload(chain: &mut Chain, data: &[u8]) -> U256 {
    let out = chain.ok("beginUpload", ASSERTER, encode("beginUpload(uint256)", |a| a.uint(U256::from(data.len()))), U256::ZERO);
    let id = Chain::word(&out, 0);
    for chunk in data.chunks(32 << 13) {
        chain.ok("upload chunk", ASSERTER, encode("upload(uint256,bytes)", |a| a.uint(id).bytes(chunk)), U256::ZERO);
    }
    let out = chain.ok("finishUpload", ASSERTER, encode("finishUpload(uint256)", |a| a.uint(id)), U256::ZERO);
    let root = B256::from_slice(&out.output[..32]);
    assert_eq!(root, levels(&words_of(data), BODY_DEPTH)[BODY_DEPTH][0], "the on-chain upload root matches");
    return id;
}

fn assert_lift(chain: &mut Chain, scenario: &Scenario, data: U256, steps: u64) -> u64 {
    let out = chain.ok(
        "assertLift",
        ASSERTER,
        encode("assertLift(bytes,uint256,bytes,uint256,uint256)", |a| {
            a.bytes(&scenario.output).uint(scenario.counts).bytes(BINDING).uint(data).uint(U256::from(steps))
        }),
        ether(1),
    );
    return Chain::word(&out, 0).to::<u64>();
}

fn main() {
    let n: usize = env::args().nth(1).map_or(219, |s| s.parse().expect("responses"));
    let cache = env::args().nth(2).expect("lift cache file");
    let arity: u64 = env::args().nth(3).map_or(16, |s| s.parse().expect("arity"));
    let t0 = Instant::now();
    let mut machine = Machine::new(false);
    let scenario = Scenario::new(&mut machine, n, &cache);
    let stream_body = Arc::new(levels(&words_of(&scenario.stream.segments[0]), BODY_DEPTH));
    let stream_root = stream_body[BODY_DEPTH][0];
    let on = deploy(&mut machine, &scenario, stream_root);
    let mut deploy_gas: Vec<(String, u64)> = on.gas.clone();
    let mut args = pofseed_flock_lift_evm::evm::Abi::default()
        .uint(U256::from_be_slice(on.onestep.as_slice()))
        .uint(ether(1))
        .uint(U256::from(WINDOW))
        .uint(U256::from(MOVE))
        .uint(U256::from(arity))
        .finish(Vec::new());
    let mut code = artifact("Dispute.sol", "Dispute");
    code.append(&mut args);
    let (dispute, g) = machine.deploy(code);
    deploy_gas.push(("dispute contract".into(), g));
    for (label, gas) in &deploy_gas {
        println!("deploy {label}: {gas} gas");
        assert!(*gas <= CAP, "{label} exceeds the cap");
    }
    machine.fund(ASSERTER, ether(1000));
    machine.fund(CHALLENGER, ether(1000));
    let mut chain = Chain {
        machine,
        dispute,
        gas: BTreeMap::new(),
        now: 1_800_000_000,
    };
    chain.advance(0);

    let t = Instant::now();
    let valid = Oracle::new(&mut chain.machine, &scenario, scenario.proof.clone(), &stream_body);
    assert_eq!(valid.end, ACCEPTED, "the valid proof's trace accepts");
    let total = valid.len();
    println!("valid trace: {total} steps ({:?} per call), counted in {:.1} s", valid.steps, t.elapsed().as_secs_f64());
    let mut tampered_bytes = scenario.proof.clone();
    let flip = tampered_bytes.len() / 2;
    tampered_bytes[flip] ^= 0x01;
    let t = Instant::now();
    let tampered = Oracle::new(&mut chain.machine, &scenario, tampered_bytes.clone(), &stream_body);
    assert_ne!(tampered.end, ACCEPTED, "the tampered proof's trace rejects");
    println!("tampered trace: rejects after {} steps ({:?} per call), in {:.1} s", tampered.len(), tampered.steps, t.elapsed().as_secs_f64());

    // The honest path: upload, assert, wait, confirm.
    let valid_upload = upload(&mut chain, &scenario.proof);
    let honest = assert_lift(&mut chain, &scenario, valid_upload, total);
    let early = chain.send("confirm (early)", ASSERTER, encode("confirm(uint256)", |a| a.uint(U256::from(honest))), U256::ZERO);
    assert!(!early.success, "confirming inside the window is refused");
    let tampered_upload = upload(&mut chain, &tampered_bytes);

    let s0 = valid.steps[0];
    let s01 = s0 + valid.steps[1];
    let s012 = s01 + valid.steps[2];
    let r = tampered.len();
    let mut cases = vec![
        ("lie from the first step", Proof::Valid, total, Asserter::LiesFrom(1), Challenger::Honest, true, false),
        ("lie at the lift contract's return", Proof::Valid, total, Asserter::LiesFrom(s0), Challenger::Honest, true, false),
        ("lie inside the Keccak part", Proof::Valid, total, Asserter::LiesFrom(s0 + valid.steps[1] / 3), Challenger::Honest, true, false),
        ("lie in the middle of the stream", Proof::Valid, total, Asserter::LiesFrom(s01 + valid.steps[2] / 2), Challenger::Honest, true, false),
        ("lie inside the final check", Proof::Valid, total, Asserter::LiesFrom(s012 + 12345), Challenger::Honest, true, false),
        ("lie at the last state", Proof::Valid, total, Asserter::LiesFrom(total - 1), Challenger::Honest, true, true),
        ("claim one step too few", Proof::Valid, total - 1, Asserter::Honest, Challenger::Honest, true, false),
        ("invalid proof, consistent until the failing check", Proof::Tampered, total, Asserter::LiesFrom(r), Challenger::Honest, true, true),
        ("invalid proof, short claimed trace", Proof::Tampered, r, Asserter::LiesFrom(r), Challenger::Honest, true, false),
        ("honest asserter, challenger always picks the last interval", Proof::Valid, total, Asserter::Honest, Challenger::Last, false, true),
        ("honest asserter, challenger picks at random", Proof::Valid, total, Asserter::Honest, Challenger::Random, false, true),
        ("honest asserter, challenger stops moving", Proof::Valid, total, Asserter::Honest, Challenger::Silent, false, true),
        ("lying asserter stops moving", Proof::Valid, total, Asserter::Silent, Challenger::Honest, true, false),
    ]
    .into_iter()
    .enumerate()
    .map(|(i, (name, proof, steps, asserter, challenger, win, resolver))| Case {
        name,
        proof,
        steps,
        asserter,
        challenger,
        challenger_should_win: win,
        resolver_is_asserter: resolver,
        assertion: 0,
        game: 0,
        lo: 0,
        hi: steps,
        mids: Vec::new(),
        turn: 0,
        done: false,
        challenger_won: None,
        rounds: 0,
        seed: 0x2545_f491_4f6c_dd1d ^ i as u64,
    })
    .collect::<Vec<_>>();
    for case in cases.iter_mut() {
        let data = if case.proof == Proof::Valid { valid_upload } else { tampered_upload };
        case.assertion = assert_lift(&mut chain, &scenario, data, case.steps);
        let out = chain.ok("challenge", CHALLENGER, encode("challenge(uint256)", |a| a.uint(U256::from(case.assertion))), ether(1));
        case.game = Chain::word(&out, 0).to::<u64>();
    }

    let oracle = |p: Proof| -> &Oracle { if p == Proof::Valid { &valid } else { &tampered } };
    let claim = |case: &Case, truth: &BTreeMap<u64, B256>, g: u64| -> B256 {
        if g >= case.steps {
            return terminal(ACCEPTED);
        }
        return match case.asserter {
            Asserter::LiesFrom(from) if g >= from => fake(g),
            _ => truth[&g],
        };
    };
    let mut truths: [BTreeMap<u64, B256>; 2] = [BTreeMap::new(), BTreeMap::new()];
    let mut round = 0;
    loop {
        round += 1;
        let live: Vec<usize> = (0..cases.len()).filter(|&i| !cases[i].done && cases[i].hi - cases[i].lo >= 2).collect();
        if live.is_empty() {
            break;
        }
        let t = Instant::now();
        let mut wanted: [BTreeSet<u64>; 2] = [BTreeSet::new(), BTreeSet::new()];
        for &i in &live {
            let c = &cases[i];
            let which = if c.proof == Proof::Valid { 0 } else { 1 };
            for g in points(c.lo, c.hi, arity) {
                if !truths[which].contains_key(&g) {
                    wanted[which].insert(g);
                }
            }
        }
        for which in 0..2 {
            let o = if which == 0 { &valid } else { &tampered };
            let got = o.hashes(&mut chain.machine, &scenario, &wanted[which]);
            truths[which].extend(got);
        }
        let passes = t.elapsed().as_secs_f64();
        for &i in &live {
            let which = if cases[i].proof == Proof::Valid { 0 } else { 1 };
            let truth = &truths[which];
            let c = &cases[i];
            let p = points(c.lo, c.hi, arity);
            if let Asserter::Silent = c.asserter {
                chain.advance(0);
                continue;
            }
            let mids: Vec<B256> = p[1..p.len() - 1].iter().map(|&g| claim(c, truth, g)).collect();
            let game = c.game;
            let data = encode("dissect(uint256,bytes32[])", |a| a.uint(U256::from(game)).uints(&mids.iter().map(|h| U256::from_be_bytes(h.0)).collect::<Vec<_>>()));
            chain.ok("dissect", ASSERTER, data, U256::ZERO);
            let c = &mut cases[i];
            c.mids = mids;
            c.turn = 1;
            c.rounds += 1;
        }
        let silent_asserters: Vec<usize> = live.iter().copied().filter(|&i| matches!(cases[i].asserter, Asserter::Silent)).collect();
        chain.advance(3600);
        for &i in &live {
            if cases[i].turn != 1 {
                continue;
            }
            let which = if cases[i].proof == Proof::Valid { 0 } else { 1 };
            let truth = &truths[which];
            let c = &cases[i];
            let p = points(c.lo, c.hi, arity);
            let k = p.len() - 1;
            let right = |j: usize| -> B256 { if j == k { claim(c, truth, p[k]) } else { c.mids[j - 1] } };
            let real = |g: u64| -> B256 { if g >= oracle(c.proof).len() { terminal(oracle(c.proof).end) } else { truth[&g] } };
            let j = match c.challenger {
                Challenger::Honest => (0..k).find(|&j| right(j + 1) != real(p[j + 1])).expect("the asserter lied somewhere"),
                Challenger::Last => k - 1,
                Challenger::Random => (c.seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(round) >> 33) as usize % k,
                Challenger::Silent => continue,
            };
            let game = c.game;
            let mids = c.mids.clone();
            let data = encode("choose(uint256,bytes32[],uint256)", |a| {
                a.uint(U256::from(game)).uints(&mids.iter().map(|h| U256::from_be_bytes(h.0)).collect::<Vec<_>>()).uint(U256::from(j))
            });
            chain.ok("choose", CHALLENGER, data, U256::ZERO);
            let c = &mut cases[i];
            c.lo = p[j];
            c.hi = p[j + 1];
            c.turn = 0;
        }
        chain.advance(3600);
        // Timeouts: a side that did not move loses once its deadline passes.
        let stalled: Vec<usize> = live
            .iter()
            .copied()
            .filter(|&i| silent_asserters.contains(&i) || (cases[i].turn == 1 && matches!(cases[i].challenger, Challenger::Silent)))
            .collect();
        if !stalled.is_empty() {
            let mut until = chain.now;
            for &i in &stalled {
                let game = cases[i].game;
                let q = chain.machine.call(chain.dispute, encode("games(uint256)", |a| a.uint(U256::from(game))));
                until = until.max(Chain::word(&q, 8).to::<u64>());
            }
            chain.advance(until - chain.now);
            for i in stalled {
                let game = cases[i].game;
                let out = chain.ok("timeout", CHALLENGER, encode("timeout(uint256)", |a| a.uint(U256::from(game))), U256::ZERO);
                let _ = out;
                let challenger_won = matches!(cases[i].asserter, Asserter::Silent);
                cases[i].challenger_won = Some(challenger_won);
                cases[i].done = true;
            }
        }
        println!("round {round}: {} live games, truth passes {passes:.1} s", live.len());
    }

    // One-step resolution.
    let t = Instant::now();
    let mut wanted: [Vec<(u64, u64)>; 2] = [Vec::new(), Vec::new()];
    for c in cases.iter().filter(|c| !c.done) {
        wanted[if c.proof == Proof::Valid { 0 } else { 1 }].push((c.game, c.lo));
    }
    let inputs: [BTreeMap<u64, (Vec<u8>, usize)>; 2] = [
        valid.resolve_inputs(&mut chain.machine, &scenario, &wanted[0]),
        tampered.resolve_inputs(&mut chain.machine, &scenario, &wanted[1]),
    ];
    println!("resolution inputs built in {:.1} s", t.elapsed().as_secs_f64());
    let mut heaviest = (0u64, "", 0usize);
    for c in cases.iter_mut().filter(|c| !c.done) {
        let (data, words) = inputs[if c.proof == Proof::Valid { 0 } else { 1 }][&c.game].clone();
        let from = if c.resolver_is_asserter { ASSERTER } else { CHALLENGER };
        let out = chain.ok("resolve", from, data, U256::ZERO);
        if out.gas > heaviest.0 {
            heaviest = (out.gas, c.name, words);
        }
        let game = c.game;
        let q = chain.machine.call(chain.dispute, encode("games(uint256)", |a| a.uint(U256::from(game))));
        let won = Chain::word(&q, 9) == U256::from(1);
        c.challenger_won = Some(won);
        c.done = true;
    }

    // Refused moves, and the honest assertion's confirmation.
    chain.advance(WINDOW);
    let late = chain.send("challenge (late)", CHALLENGER, encode("challenge(uint256)", |a| a.uint(U256::from(honest))), ether(1));
    assert!(!late.success, "a challenge after the window is refused");
    chain.ok("confirm", ASSERTER, encode("confirm(uint256)", |a| a.uint(U256::from(honest))), U256::ZERO);
    let key = chain.machine.call(
        dispute,
        encode("statementKey(bytes,uint256,bytes)", |a| a.bytes(&scenario.output).uint(scenario.counts).bytes(BINDING)),
    );
    let accepted = chain.machine.call(dispute, [keccak256("accepted(bytes32)")[..4].to_vec(), key.output.clone()].concat());
    assert_eq!(Chain::word(&accepted, 0), U256::from(1), "the confirmed statement reads as accepted");
    for c in &cases {
        let confirm = chain.send("confirm (disputed)", ASSERTER, encode("confirm(uint256)", |a| a.uint(U256::from(c.assertion))), U256::ZERO);
        assert_eq!(confirm.success, !c.challenger_should_win, "{}: confirmation after the dispute", c.name);
    }

    println!("games (arity {arity}):");
    let mut failures = 0;
    for c in &cases {
        let won = c.challenger_won.expect("settled");
        let good = won == c.challenger_should_win;
        failures += usize::from(!good);
        println!(
            "  {} {:<62} {:>2} dissections, {} wins, final interval [{}, {}]",
            if good { "ok  " } else { "FAIL" },
            c.name,
            c.rounds,
            if won { "challenger" } else { "asserter" },
            c.lo,
            c.hi
        );
    }
    println!("heaviest resolve: {} gas ({}, {} words proved)", heaviest.0, heaviest.1, heaviest.2);
    println!("transactions (count, min, max gas):");
    for (label, gas) in &chain.gas {
        println!("  {label:<22} {:>3} {:>10} {:>10}", gas.len(), gas.iter().min().unwrap(), gas.iter().max().unwrap());
    }
    println!("simulation took {:.1} s", t0.elapsed().as_secs_f64());
    assert_eq!(failures, 0, "every game ends with the truthful side winning");
}
