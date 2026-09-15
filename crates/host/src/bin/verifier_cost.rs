// SPDX-License-Identifier: LGPL-3.0-or-later

//! Breaks one hardened-child chunk proof down by component size and, when built with the `count`
//! feature, its verification down by field multiplications and hash compressions per phase.
//!
//! Usage: `verifier-cost [responses]` (default 8).

use std::{env, sync::Arc};

use flock_prover::field::F128;
use pofseed_flock_lift::chunk_rm::{prove_chunk, verify_chunk};
use pofseed_flock_lift_block::{native, program::Program};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use rayon::prelude::*;

const DOMAIN: &[u8] = b"pofseed-flock-lift-verifier-cost";

fn size<T: serde::Serialize>(value: &T) -> usize {
    return bincode::serialize(value).expect("serialise").len();
}

fn main() {
    let n: usize = env::args().nth(1).map(|a| a.parse().expect("response count")).unwrap_or(8);
    let (_, output, proof) = vector_1_proof(n, b"verifier-cost", b"");
    let (_, chain_code) = bip32_vector_1();
    let public = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let program = Arc::new(Program::new(&public));
    let publics: Vec<Vec<F128>> = proof
        .par_iter()
        .map(|r| native::io_words(&program, &public, &output, r).expect("native replay"))
        .collect();
    let chunk = prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
    let lig = &chunk.opening.ligerito;
    println!("chunk of {n} responses, m = {}", chunk.commitment.params.m);
    println!("  whole chunk proof      {:>9} B", size(&chunk));
    println!("  zerocheck              {:>9} B", size(&chunk.zerocheck));
    println!("  lincheck               {:>9} B", size(&chunk.lincheck));
    println!("  commitment             {:>9} B", size(&chunk.commitment));
    println!("  ring switches          {:>9} B", size(&chunk.opening.ring_switches));
    println!("  Ligerito (bincode)     {:>9} B", size(lig));
    println!("  Ligerito (size_bytes)  {:>9} B", lig.size_bytes());
    let rows = |r: &Vec<Vec<F128>>| r.iter().map(|x| x.len() * 16).sum::<usize>();
    println!(
        "    level 0: {} opened rows of {} words = {} B, Merkle {} B",
        lig.initial_proof.opened_rows.len(),
        lig.initial_proof.opened_rows.first().map_or(0, |r| r.len()),
        rows(&lig.initial_proof.opened_rows),
        lig.initial_proof.merkle_proof.len() * 32
    );
    for (i, p) in lig.recursive_proofs.iter().enumerate() {
        println!(
            "    level {}: {} opened rows of {} words = {} B, Merkle {} B",
            i + 1,
            p.opened_rows.len(),
            p.opened_rows.first().map_or(0, |r| r.len()),
            rows(&p.opened_rows),
            p.merkle_proof.len() * 32
        );
    }
    println!("  published words        {:>9} B", publics.len() * publics[0].len() * 16);
    verify_chunk(&program, &publics, &chunk, DOMAIN).expect("verify");
    println!("verified");
}
