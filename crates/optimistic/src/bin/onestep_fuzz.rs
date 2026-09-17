// SPDX-License-Identifier: LGPL-3.0-or-later

//! Differential fuzzing of the one-step contract against revm on random programs.
//!
//! Usage: `onestep-fuzz [programs] [seed]`.

use std::env;

use pofseed_flock_lift_optimistic::fuzz::run;

fn main() {
    let programs: usize = env::args().nth(1).map_or(300, |s| s.parse().expect("programs"));
    let seed: u64 = env::args().nth(2).map_or(0x5eed_1234_abcd_0001, |s| s.parse().expect("seed"));
    let r = run(programs, seed, true);
    println!(
        "{} programs, {} steps checked ({} continuing, {} rejecting), {} distinct opcodes, {} mismatches",
        r.programs, r.steps, r.continuing, r.rejecting, r.opcodes, r.mismatches
    );
    assert_eq!(r.mismatches, 0, "the one-step contract disagrees with revm");
}
