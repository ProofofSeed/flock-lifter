// SPDX-License-Identifier: LGPL-3.0-or-later

//! Plays the optimistic verification of a real lift end to end in revm and prints what every
//! transaction cost and how every game ended.
//!
//! Usage: `dispute-sim <responses> <lift-cache-file> [arity] [heavy-steps]`, or
//! `dispute-sim mock [arity]` for the stand-in contracts, where `heavy-steps` is a
//! comma-separated list of global steps each to be resolved in a game of its own.

use std::{env, time::Instant};

use pofseed_flock_lift_optimistic::{machine::Machine, scenario::Scenario, sim::simulate, trace::Proofs};

/// The scenario's proofs with a byte flipped in each: the first for the stand-ins, whose checks
/// look there, and the middle one otherwise.
fn tamper(scenario: &Scenario, mock: bool) -> Proofs {
    let mut lift = scenario.proof.clone();
    let mut matrix = scenario.matrix_proof.clone();
    if mock {
        lift[0] = 0xff;
        matrix[0] ^= 0x01;
    } else {
        let (l, m) = (lift.len() / 2, matrix.len() / 2);
        lift[l] ^= 0x01;
        matrix[m] ^= 0x01;
    }
    return Proofs { lift, matrix };
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let t = Instant::now();
    let mut machine = Machine::new(false);
    let mut heavy: Vec<u64> = Vec::new();
    let (scenario, tampered, arity) = if args.get(1).map(String::as_str) == Some("mock") {
        let scenario = Scenario::mock(&mut machine);
        let tampered = tamper(&scenario, true);
        (scenario, tampered, args.get(2).map_or(16, |s| s.parse().expect("arity")))
    } else {
        let n: usize = args.get(1).map_or(219, |s| s.parse().expect("responses"));
        let scenario = Scenario::new(&mut machine, n, args.get(2).expect("lift cache file"));
        let tampered = tamper(&scenario, false);
        heavy = args.get(4).map(|s| s.split(',').filter(|x| !x.is_empty()).map(|x| x.parse().expect("step")).collect()).unwrap_or_default();
        (scenario, tampered, args.get(3).map_or(16, |s| s.parse().expect("arity")))
    };
    let report = simulate(machine, &scenario, tampered, arity, &heavy, true);
    for (label, gas) in &report.deploy_gas {
        println!("deploy {label}: {gas} gas");
    }
    println!(
        "valid trace {:?} steps per call, {} in all; tampered lift rejects after {}, tampered matrix proof after {}",
        report.steps,
        report.steps.iter().sum::<u64>(),
        report.tampered_lift_steps,
        report.tampered_matrix_steps
    );
    println!(
        "truth passes per round (s): {:?}; resolution inputs {:.1} s",
        report.round_secs.iter().map(|s| (s * 10.0).round() / 10.0).collect::<Vec<_>>(),
        report.resolve_secs
    );
    println!("games (arity {arity}):");
    for g in &report.games {
        println!(
            "  {} {:<62} {:>2} dissections, {} wins, final interval [{}, {}]",
            if g.ok { "ok  " } else { "FAIL" },
            g.name,
            g.dissections,
            if g.challenger_won { "challenger" } else { "asserter" },
            g.interval.0,
            g.interval.1
        );
    }
    println!("heaviest resolve: {} gas ({}, {} words proved)", report.heaviest.0, report.heaviest.1, report.heaviest.2);
    println!("transactions (count, min, max gas):");
    for (label, gas) in &report.gas {
        println!("  {label:<22} {:>3} {:>10} {:>10}", gas.len(), gas.iter().min().unwrap(), gas.iter().max().unwrap());
    }
    println!("simulation took {:.1} s", t.elapsed().as_secs_f64());
    assert!(report.games.iter().all(|g| g.ok), "every game ends with the truthful side winning");
}
