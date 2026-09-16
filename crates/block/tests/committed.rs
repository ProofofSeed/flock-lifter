// SPDX-License-Identifier: LGPL-3.0-or-later

//! The committed-matrix entries of a block against the explicit rows they stand for.

use flock_prover::field::F128;
use pofseed_flock_lift_block::{
    committed::{Tables, entries, value},
    program::Program,
    toy::Toy,
};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use zkboo::circuit::Circuit;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        return self.0;
    }

    fn f128(&mut self) -> F128 {
        return F128::new(self.next(), self.next());
    }
}

fn check<C: Circuit>(build: fn(&C) -> Program, circuit: &C, rounds: usize) {
    let program = build(circuit);
    let list = entries(&program);
    let (na, nb) = program.explicit_nnz();
    println!(
        "{} explicit rows, {} nonzeros, {} entries",
        program.explicit_rows(),
        na + nb,
        list.len()
    );
    let mut rng = Rng(0x243f_6a88_85a3_08d3);
    for _ in 0..rounds {
        let alpha = rng.f128();
        let skip: Vec<F128> = (0..64).map(|_| rng.f128()).collect();
        let z: Vec<F128> = (0..64).map(|_| rng.f128()).collect();
        let rest = program.geometry().k_log() - 6;
        let x: Vec<F128> = (0..rest).map(|_| rng.f128()).collect();
        let r: Vec<F128> = (0..rest).map(|_| rng.f128()).collect();
        let explicit = program.comb_explicit(alpha, &skip, &x, &r);
        let expected = explicit.iter().zip(&z).fold(F128::ZERO, |acc, (&c, &w)| acc + c * w);
        assert_eq!(value(&list, &Tables::new(alpha, &skip, &z, &x, &r)), expected);
        assert_ne!(expected, F128::ZERO, "the explicit rows contribute");
    }
}

fn hardened_child() -> HardenedChildCircuit {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    return HardenedChildCircuit::public_only(chain_code, 0x8000_0000);
}

#[test]
fn toy_compact_entries_match_the_explicit_rows() {
    check(Program::compact, &Toy, 3);
}

#[test]
fn toy_entries_match_the_explicit_rows() {
    check(Program::new, &Toy, 3);
}

#[test]
#[ignore]
fn hardened_child_entries_match_the_explicit_rows() {
    check(Program::new, &hardened_child(), 2);
}

#[test]
#[ignore]
fn hardened_child_compact_entries_match_the_explicit_rows() {
    check(Program::compact, &hardened_child(), 1);
}
