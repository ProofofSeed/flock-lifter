// SPDX-License-Identifier: LGPL-3.0-or-later

//! The optimistic verification of a scenario played end to end: the proof's upload, an
//! unchallenged assertion confirmed after its window, and a set of disputed assertions in which
//! honest and dishonest asserters and challengers meet, every game played to its end. Every
//! transaction runs under mainnet's 2^24 gas cap and is metered.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::Instant,
};

use pofseed_flock_lift_evm::evm::{Abi, artifact, encode};
use revm::primitives::{Address, B256, U256, keccak256};

use crate::{
    deploy::deploy,
    game::Oracle,
    machine::{Machine, Outcome},
    merkle::{levels, words_of},
    scenario::{BINDING, Scenario},
    vm::{ACCEPTED, BODY_DEPTH, terminal},
};

/// The asserter's address.
pub const ASSERTER: Address = Address::new([0xa5; 20]);
/// The challenger's address.
pub const CHALLENGER: Address = Address::new([0xc4; 20]);
/// Seconds in a day.
pub const DAY: u64 = 86_400;
/// The challenge window assumed.
pub const WINDOW: u64 = 7 * DAY;
/// The time per move assumed.
pub const MOVE: u64 = DAY;
/// The transaction gas cap.
pub const CAP: u64 = 1 << 24;
/// Upload chunk size in bytes, as `Dispute.CHUNK_DEPTH` sets it.
pub const UPLOAD_CHUNK: usize = 32 << 13;

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
    /// The first sub-interval whose right end the asserter got wrong, or the last if none is.
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

/// A game's outcome.
#[derive(Clone, Debug)]
pub struct GameReport {
    /// What the game tests.
    pub name: String,
    /// Whether the side that told the truth won.
    pub ok: bool,
    /// Dissections the asserter made.
    pub dissections: usize,
    /// Whether the challenger won.
    pub challenger_won: bool,
    /// The last interval.
    pub interval: (u64, u64),
}

/// What a simulation measured.
#[derive(Clone, Debug, Default)]
pub struct Report {
    /// Gas of each one-off deployment.
    pub deploy_gas: Vec<(String, u64)>,
    /// Steps of each call of the valid trace.
    pub steps: Vec<u64>,
    /// Steps before the tampered trace rejects.
    pub tampered_steps: u64,
    /// Seconds to count the valid trace.
    pub count_secs: f64,
    /// Seconds of truth passes per round.
    pub round_secs: Vec<f64>,
    /// Seconds to build the resolution inputs.
    pub resolve_secs: f64,
    /// Gas of every transaction, by kind.
    pub gas: BTreeMap<String, Vec<u64>>,
    /// Every game's outcome.
    pub games: Vec<GameReport>,
    /// The heaviest resolution: gas, game and words proved.
    pub heaviest: (u64, String, usize),
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
        assert!(out.success, "{label} failed: {}", String::from_utf8_lossy(&out.output));
        return out;
    }

    fn advance(&mut self, secs: u64) {
        self.now += secs;
        self.machine.set_time(self.now);
    }

    fn word(out: &Outcome, i: usize) -> U256 {
        return U256::from_be_slice(&out.output[32 * i..32 * i + 32]);
    }

    fn game_word(&mut self, game: u64, i: usize) -> U256 {
        let q = self.machine.call(self.dispute, encode("games(uint256)", |a| a.uint(U256::from(game))));
        return Self::word(&q, i);
    }
}

/// The step indices that dissect `[lo, hi)` into at most `arity` parts, ends included, as
/// `Dispute.points` computes them.
pub fn points(lo: u64, hi: u64, arity: u64) -> Vec<u64> {
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
    for chunk in data.chunks(UPLOAD_CHUNK) {
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

fn words(hashes: &[B256]) -> Vec<U256> {
    return hashes.iter().map(|h| U256::from_be_bytes(h.0)).collect();
}

/// Plays the scenario's optimistic verification in `machine` with dissections of `arity`,
/// `tampered` being a proof the verification rejects. Panics if a transaction breaks the cap.
pub fn simulate(mut machine: Machine, scenario: &Scenario, tampered_bytes: Vec<u8>, arity: u64, verbose: bool) -> Report {
    let mut report = Report::default();
    let stream_body = Arc::new(levels(&words_of(&scenario.stream.segments[0]), BODY_DEPTH));
    let stream_root = stream_body[BODY_DEPTH][0];
    let on = deploy(&mut machine, scenario, stream_root);
    report.deploy_gas = on.gas.clone();
    let args = Abi::default()
        .uint(U256::from_be_slice(on.onestep.as_slice()))
        .uint(ether(1))
        .uint(U256::from(WINDOW))
        .uint(U256::from(MOVE))
        .uint(U256::from(arity))
        .finish(Vec::new());
    let mut code = artifact("Dispute.sol", "Dispute");
    code.extend_from_slice(&args);
    let (dispute, g) = machine.deploy(code);
    report.deploy_gas.push(("dispute contract".into(), g));
    for (label, gas) in &report.deploy_gas {
        assert!(*gas <= CAP, "deploying the {label} exceeds the cap");
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
    let valid = Oracle::new(&mut chain.machine, scenario, scenario.proof.clone(), &stream_body);
    assert_eq!(valid.end, ACCEPTED, "the valid proof's trace accepts");
    report.count_secs = t.elapsed().as_secs_f64();
    report.steps = valid.steps.clone();
    let total = valid.len();
    let tampered = Oracle::new(&mut chain.machine, scenario, tampered_bytes.clone(), &stream_body);
    assert_ne!(tampered.end, ACCEPTED, "the tampered proof's trace rejects");
    report.tampered_steps = tampered.len();
    if verbose {
        println!("valid trace: {total} steps ({:?} per call), counted in {:.1} s", valid.steps, report.count_secs);
        println!("tampered trace: rejects after {} steps", tampered.len());
    }

    let valid_upload = upload(&mut chain, &scenario.proof);
    let honest = assert_lift(&mut chain, scenario, valid_upload, total);
    let early = chain.send("confirm (early)", ASSERTER, encode("confirm(uint256)", |a| a.uint(U256::from(honest))), U256::ZERO);
    assert!(!early.success, "confirming inside the window is refused");
    let tampered_upload = upload(&mut chain, &tampered_bytes);

    let st = &valid.steps;
    let (s0, s01, s012) = (st[0], st[0] + st[1], st[0] + st[1] + st[2]);
    let r = tampered.len();
    let mut cases: Vec<Case> = vec![
        ("lie from the first step", Proof::Valid, total, Asserter::LiesFrom(1), Challenger::Honest, true, false),
        ("lie at the lift contract's return", Proof::Valid, total, Asserter::LiesFrom(s0), Challenger::Honest, true, false),
        ("lie inside the Keccak part", Proof::Valid, total, Asserter::LiesFrom(s0 + st[1] / 3), Challenger::Honest, true, false),
        ("lie in the middle of the stream", Proof::Valid, total, Asserter::LiesFrom(s01 + st[2] / 2), Challenger::Honest, true, false),
        ("lie inside the final check", Proof::Valid, total, Asserter::LiesFrom(s012 + st[3] / 2), Challenger::Honest, true, false),
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
    .collect();
    for case in cases.iter_mut() {
        let data = if case.proof == Proof::Valid { valid_upload } else { tampered_upload };
        case.assertion = assert_lift(&mut chain, scenario, data, case.steps);
        let out = chain.ok("challenge", CHALLENGER, encode("challenge(uint256)", |a| a.uint(U256::from(case.assertion))), ether(1));
        case.game = Chain::word(&out, 0).to::<u64>();
    }

    let oracles = [&valid, &tampered];
    let which = |p: Proof| -> usize { if p == Proof::Valid { 0 } else { 1 } };
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
    let mut round = 0u64;
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
            for g in points(c.lo, c.hi, arity) {
                if !truths[which(c.proof)].contains_key(&g) {
                    wanted[which(c.proof)].insert(g);
                }
            }
        }
        for w in 0..2 {
            let got = oracles[w].hashes(&mut chain.machine, scenario, &wanted[w]);
            truths[w].extend(got);
        }
        report.round_secs.push(t.elapsed().as_secs_f64());
        for &i in &live {
            let c = &cases[i];
            if let Asserter::Silent = c.asserter {
                continue;
            }
            let p = points(c.lo, c.hi, arity);
            let mids: Vec<B256> = p[1..p.len() - 1].iter().map(|&g| claim(c, &truths[which(c.proof)], g)).collect();
            let game = c.game;
            chain.ok("dissect", ASSERTER, encode("dissect(uint256,bytes32[])", |a| a.uint(U256::from(game)).uints(&words(&mids))), U256::ZERO);
            let c = &mut cases[i];
            c.mids = mids;
            c.turn = 1;
            c.rounds += 1;
        }
        chain.advance(3600);
        for &i in &live {
            if cases[i].turn != 1 {
                continue;
            }
            let c = &cases[i];
            let truth = &truths[which(c.proof)];
            let oracle = oracles[which(c.proof)];
            let p = points(c.lo, c.hi, arity);
            let k = p.len() - 1;
            let right = |j: usize| -> B256 { if j == k { claim(c, truth, p[k]) } else { c.mids[j - 1] } };
            let real = |g: u64| -> B256 { if g >= oracle.len() { terminal(oracle.end) } else { truth[&g] } };
            let j = match c.challenger {
                Challenger::Honest => (0..k).find(|&j| right(j + 1) != real(p[j + 1])).unwrap_or(k - 1),
                Challenger::Last => k - 1,
                Challenger::Random => (c.seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(round) >> 33) as usize % k,
                Challenger::Silent => continue,
            };
            let (game, mids) = (c.game, c.mids.clone());
            chain.ok(
                "choose",
                CHALLENGER,
                encode("choose(uint256,bytes32[],uint256)", |a| a.uint(U256::from(game)).uints(&words(&mids)).uint(U256::from(j))),
                U256::ZERO,
            );
            let c = &mut cases[i];
            c.lo = p[j];
            c.hi = p[j + 1];
            c.turn = 0;
            let (lo, hi) = (chain.game_word(game, 2).to::<u64>(), chain.game_word(game, 3).to::<u64>());
            assert_eq!((lo, hi), (c.lo, c.hi), "the contract narrowed the interval as expected");
        }
        chain.advance(3600);
        let stalled: Vec<usize> = live
            .iter()
            .copied()
            .filter(|&i| matches!(cases[i].asserter, Asserter::Silent) || (cases[i].turn == 1 && matches!(cases[i].challenger, Challenger::Silent)))
            .collect();
        if !stalled.is_empty() {
            let mut until = chain.now;
            for &i in &stalled {
                until = until.max(chain.game_word(cases[i].game, 8).to::<u64>());
            }
            let early = chain.send("timeout (early)", CHALLENGER, encode("timeout(uint256)", |a| a.uint(U256::from(cases[stalled[0]].game))), U256::ZERO);
            assert!(!early.success, "a timeout before the deadline is refused");
            chain.advance(until - chain.now);
            for i in stalled {
                let game = cases[i].game;
                chain.ok("timeout", CHALLENGER, encode("timeout(uint256)", |a| a.uint(U256::from(game))), U256::ZERO);
                cases[i].challenger_won = Some(chain.game_word(game, 9) == U256::from(1));
                cases[i].done = true;
            }
        }
        if verbose {
            println!("round {round}: {} live games, truth passes {:.1} s", live.len(), report.round_secs.last().unwrap());
        }
    }

    let t = Instant::now();
    let mut wanted: [Vec<(u64, u64)>; 2] = [Vec::new(), Vec::new()];
    for c in cases.iter().filter(|c| !c.done) {
        wanted[which(c.proof)].push((c.game, c.lo));
    }
    let inputs = [
        valid.resolve_inputs(&mut chain.machine, scenario, &wanted[0]),
        tampered.resolve_inputs(&mut chain.machine, scenario, &wanted[1]),
    ];
    report.resolve_secs = t.elapsed().as_secs_f64();
    for c in cases.iter_mut().filter(|c| !c.done) {
        let (data, words) = inputs[which(c.proof)][&c.game].clone();
        let from = if c.resolver_is_asserter { ASSERTER } else { CHALLENGER };
        let out = chain.ok("resolve", from, data, U256::ZERO);
        if out.gas > report.heaviest.0 {
            report.heaviest = (out.gas, c.name.to_string(), words);
        }
        c.challenger_won = Some(chain.game_word(c.game, 9) == U256::from(1));
        c.done = true;
    }

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
        let won = c.challenger_won.expect("settled");
        assert_eq!(confirm.success, !won, "{}: confirmation after the dispute follows its outcome", c.name);
        report.games.push(GameReport {
            name: c.name.to_string(),
            ok: won == c.challenger_should_win,
            dissections: c.rounds,
            challenger_won: won,
            interval: (c.lo, c.hi),
        });
    }
    report.gas = chain.gas;
    return report;
}
