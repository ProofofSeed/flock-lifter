// SPDX-License-Identifier: LGPL-3.0-or-later

//! Plays the optimistic verification of a real lift end to end in revm and prints what every
//! transaction cost and how every game ended.
//!
//! Usage: `dispute-sim <responses> <lift-cache-file> [arity]`, or `dispute-sim mock [arity]` for
//! the stand-in contracts.

use std::{env, time::Instant};

use pofseed_flock_lift_optimistic::{machine::Machine, scenario::Scenario, sim::simulate};

fn main() {
    let args: Vec<String> = env::args().collect();
    let t = Instant::now();
    let mut machine = Machine::new(false);
    let (scenario, tampered, arity) = if args.get(1).map(String::as_str) == Some("mock") {
        let scenario = Scenario::mock(&mut machine);
        let mut tampered = scenario.proof.clone();
        tampered[0] = 0xff;
        (scenario, tampered, args.get(2).map_or(16, |s| s.parse().expect("arity")))
    } else {
        let n: usize = args.get(1).map_or(219, |s| s.parse().expect("responses"));
        let scenario = Scenario::new(&mut machine, n, args.get(2).expect("lift cache file"));
        let mut tampered = scenario.proof.clone();
        let flip = tampered.len() / 2;
        tampered[flip] ^= 0x01;
        (scenario, tampered, args.get(3).map_or(16, |s| s.parse().expect("arity")))
    };
    let report = simulate(machine, &scenario, tampered, arity, true);
    for (label, gas) in &report.deploy_gas {
        println!("deploy {label}: {gas} gas");
    }
    println!(
        "valid trace {:?} steps per call, {} in all; tampered trace rejects after {}",
        report.steps,
        report.steps.iter().sum::<u64>(),
        report.tampered_steps
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
