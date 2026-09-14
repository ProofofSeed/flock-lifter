// SPDX-License-Identifier: LGPL-3.0-or-later

//! Proves and verifies one Flock chunk over hardened-child responses, reporting the block, the
//! time of each phase and the proof size.
//!
//! Usage: `chunk-probe [responses] [union|row-major]` (default 8, union).

use std::{env, sync::Arc, time::Instant};

use flock_prover::field::F128;
use pofseed_flock_lift::{chunk, chunk_rm};
use pofseed_flock_lift_block::{native, program::Program};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use rayon::prelude::*;

const DOMAIN: &[u8] = b"pofseed-flock-lift-chunk-probe";

fn main() {
    let n: usize = env::args().nth(1).map(|a| a.parse().expect("response count")).unwrap_or(8);
    let path = env::args().nth(2).unwrap_or_else(|| "union".into());
    let t = Instant::now();
    let (_, output, proof) = vector_1_proof(n, b"chunk-probe", b"");
    println!("zkboo proof of {n} responses: {:.2} s", t.elapsed().as_secs_f64());
    let (_, chain_code) = bip32_vector_1();
    let public = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let t = Instant::now();
    let program = Arc::new(Program::new(&public));
    let g = program.geometry();
    println!(
        "response block: k_log {}, {} Keccak-f, {} products, {} materialised, {} explicit rows ({:.2} s)",
        g.k_log(),
        g.keccak_subs(),
        program.replay_products(),
        program.replay_materialised(),
        program.explicit_rows(),
        t.elapsed().as_secs_f64()
    );
    let publics: Vec<Vec<F128>> = proof
        .par_iter()
        .map(|r| native::io_words(&program, &public, &output, r).expect("native replay"))
        .collect();
    let (prove_s, verify_s, size) = match path.as_str() {
        "union" => {
            let t = Instant::now();
            let c = chunk::prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
            let prove_s = t.elapsed().as_secs_f64();
            let t = Instant::now();
            chunk::verify_chunk(&program, &publics, &c, DOMAIN).expect("verify");
            (prove_s, t.elapsed().as_secs_f64(), bincode::serialize(&c).unwrap().len())
        }
        "row-major" => {
            let t = Instant::now();
            let c = chunk_rm::prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
            let prove_s = t.elapsed().as_secs_f64();
            let t = Instant::now();
            chunk_rm::verify_chunk(&program, &publics, &c, DOMAIN).expect("verify");
            let verify_s = t.elapsed().as_secs_f64();
            let mut tampered = publics.clone();
            tampered[n / 2][3] += F128::ONE;
            assert!(chunk_rm::verify_chunk(&program, &tampered, &c, DOMAIN).is_err(), "tampered published word refused");
            (prove_s, verify_s, bincode::serialize(&c).unwrap().len())
        }
        other => panic!("unknown path {other}"),
    };
    println!("{path}: prove {prove_s:.2} s, verify {verify_s:.2} s, proof {size} B");
}
