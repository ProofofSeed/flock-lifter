// SPDX-License-Identifier: LGPL-3.0-or-later

//! Proves the chunks and the wrap of a hardened-child lift of a given size and reports how the
//! wrap circuit and the fixed tables' layout grow with it, without committing the tables.
//!
//! Usage: `batch-probe <responses> [chunk] [log inverse rate]`.

use std::{env, sync::Arc, time::Instant};

use flock_prover::{field::F128, pcs::OuterPcs, tower::HeadEnv, union::UnionInstance};
use pofseed_flock_lift::{chunk_wrap, lift::MAX_CHUNK, root::RootKey, wrap};
use pofseed_flock_lift_block::{native, program::Program};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use pofseed_flock_lift_structure::key::{Held, Layout};
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
};
use rayon::prelude::*;

fn main() {
    let n: usize = env::args().nth(1).expect("usage: batch-probe <responses> [chunk] [log inverse rate]").parse().expect("count");
    let chunk: usize = env::args().nth(2).map(|a| a.parse().expect("chunk size")).unwrap_or(MAX_CHUNK);
    let rate: usize = env::args().nth(3).map(|a| a.parse().expect("log inverse rate")).unwrap_or(6);
    let whir = WhirOuter::new(4, rate, Regime::Johnson, 3, 22, 128).with_merkle(MerkleHash::Keccak);
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter bench entropy", b"flock-lifter bench binding");
    let (_, chain_code) = bip32_vector_1();
    let circuit = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let program = Arc::new(Program::new(&circuit));
    let words: Vec<Vec<F128>> =
        proof.par_iter().map(|r| native::io_words(&program, &circuit, &output, r).expect("replay")).collect();
    let domains: Vec<Vec<u8>> =
        (0..n.div_ceil(chunk)).map(|i| format!("pofseed-flock-lift-batch-probe-{n}-{chunk}-{i}").into_bytes()).collect();
    let t = Instant::now();
    let chunks: Vec<chunk_wrap::ChunkProofWrap> = proof
        .chunks(chunk)
        .zip(words.chunks(chunk))
        .zip(&domains)
        .map(|((r, p), d)| chunk_wrap::prove_chunk(&program, r, p, d).expect("prove"))
        .collect();
    let chunks_s = t.elapsed().as_secs_f64();
    drop(proof);
    let parts: Vec<&[Vec<F128>]> = words.chunks(chunk).collect();
    let t = Instant::now();
    let w = wrap::wrap(&program, &parts, &chunks, &domains, &HeadEnv::measuring(), Some(&whir as &dyn OuterPcs)).expect("wrap");
    let wrap_s = t.elapsed().as_secs_f64();
    let tm = &w.timings;
    println!(
        "{n} responses in {} chunks of {chunk}: chunks {chunks_s:.1} s, wrap {wrap_s:.1} s (record {:.1}, tapes {:.1}, build {:.1}, witness {:.1}, prove {:.1}), wrap proof {} B",
        chunks.len(),
        tm.record,
        tm.tapes,
        tm.build,
        tm.witness,
        tm.prove,
        bincode::serialize(&w.proof).expect("a proof").len()
    );
    let shape = &w.key.key.shape;
    let reg = &shape.registry;
    let union = UnionInstance::new(reg, shape.counts.clone());
    let cells = shape.circuit.cells();
    println!(
        "wrap circuit: nu {} M {} M_bool {} M_elem {} dense_m {} mu {} gate slots {} public words {} live cells {}",
        reg.nu(),
        reg.m_total(),
        reg.m_bool(),
        reg.m_elem(),
        union.dense_m(),
        cells.mu(),
        cells.num_gate_slots(),
        shape.circuit.num_public(),
        shape.circuit.live_mask().counts.iter().sum::<usize>()
    );
    let (parts, _) = RootKey::parts(&program, &w.key);
    let layout = Layout::of(&parts);
    println!("tables: 2^{} bytes", layout.n);
    for (i, (k, held)) in layout.tables.iter().enumerate() {
        match held {
            Held::Dense(regions) => println!("  table {i} of 2^{k} columns: dense, two regions of 2^{} bytes", regions[0].log),
            Held::Small(_) => println!("  table {i} of 2^{k} columns: among the small entries"),
        }
    }
    println!(
        "  operations 2^{} and masks 2^{}, Keccak tensor 2^{}, live cells 2^{}, small entries 2^{} bytes",
        layout.ops.log, layout.masks.log, layout.kernel.log, layout.cells.log, layout.small.log
    );
}
