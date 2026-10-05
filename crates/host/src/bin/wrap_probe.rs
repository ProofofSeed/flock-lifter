// SPDX-License-Identifier: LGPL-3.0-or-later

//! Wraps the chunk proofs of a hardened-child lift and reports each phase.
//!
//! Usage: `wrap-probe <responses> [chunk] [whir-k<folding>-r<log inverse rate>|ligerito]`.

use std::{env, sync::Arc, time::Instant};

use flock_prover::{field::F128, pcs::OuterPcs, tower::HeadEnv};
use pofseed_flock_lift::{chunk_wrap, lift::MAX_CHUNK, wrap};
use pofseed_flock_lift_block::{native, program::Program};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
};
use rayon::prelude::*;

fn outer(spec: &str) -> Option<WhirOuter> {
    if spec == "ligerito" {
        return None;
    }
    let rest = spec.strip_prefix("whir-k").expect("ligerito or whir-k<k>-r<r>");
    let (k, r) = rest.split_once("-r").expect("whir-k<k>-r<r>");
    return Some(
        WhirOuter::new(k.parse().unwrap(), r.parse().unwrap(), Regime::Johnson, 6, 16, 128)
            .with_merkle(MerkleHash::Keccak),
    );
}

fn main() {
    let n: usize = env::args().nth(1).expect("usage: wrap-probe <responses> [chunk] [outer]").parse().expect("count");
    let chunk: usize = env::args().nth(2).map(|a| a.parse().expect("chunk size")).unwrap_or(MAX_CHUNK);
    let spec = env::args().nth(3).unwrap_or_else(|| "whir-k4-r1".to_string());
    let whir = outer(&spec);
    let outer: Option<&dyn OuterPcs> = whir.as_ref().map(|w| w as &dyn OuterPcs);
    #[cfg(feature = "count")]
    flock_prover::field::gf2_128::op_count::ON.store(false, std::sync::atomic::Ordering::Relaxed);
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter bench entropy", b"flock-lifter bench binding");
    let (_, chain_code) = bip32_vector_1();
    let circuit = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let program = Arc::new(Program::new(&circuit));
    let words: Vec<Vec<F128>> =
        proof.par_iter().map(|r| native::io_words(&program, &circuit, &output, r).expect("replay")).collect();
    let domains: Vec<Vec<u8>> =
        (0..n.div_ceil(chunk)).map(|i| format!("pofseed-flock-lift-wrap-probe-{n}-{chunk}-{i}").into_bytes()).collect();
    let t = Instant::now();
    let chunks: Vec<chunk_wrap::ChunkProofWrap> = proof
        .chunks(chunk)
        .zip(words.chunks(chunk))
        .zip(&domains)
        .map(|((r, p), d)| chunk_wrap::prove_chunk(&program, r, p, d).expect("prove"))
        .collect();
    let chunks_s = t.elapsed().as_secs_f64();
    drop(proof);
    let chunk_bytes: usize = chunks.iter().map(|c| bincode::serialize(c).unwrap().len()).sum();
    let parts: Vec<&[Vec<F128>]> = words.chunks(chunk).collect();
    let t = Instant::now();
    for ((c, p), d) in chunks.iter().zip(&parts).zip(&domains) {
        chunk_wrap::verify_chunk(&program, p, c, d).expect("a chunk verifies");
    }
    let chunks_verify_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let w = wrap::wrap(&program, &parts, &chunks, &domains, &HeadEnv::measuring(), outer).expect("wrap");
    let wrap_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    wrap::verify_wrapped(&program, &parts, &w.key, &w.proof, outer).expect("the wrap verifies");
    let verify_s = t.elapsed().as_secs_f64();
    #[cfg(feature = "count")]
    {
        use flock_prover::field::gf2_128::op_count;
        op_count::ON.store(true, std::sync::atomic::Ordering::Relaxed);
        op_count::phase("before");
        chunk_wrap::verify_chunk(&program, parts[0], &chunks[0], &domains[0]).expect("a chunk verifies");
        op_count::phase("chunk 0 in all (with its matrix discharge)");
        let mut ch = wrap::outer_transcript(&w.proof.public);
        let (work, _sigma) = w.key.key.verify_deferred(&w.proof, outer, &mut ch).expect("deferred verification");
        op_count::phase("deferred: merged opening in all");
        eprintln!(
            "[count] boolean types {}, element {}, layout row claims {}, layout groups {}",
            work.boolean.as_ref().map_or(0, |a| a.evals.len()),
            work.element.is_some(),
            work.jagged.rs.len(),
            work.jagged.groups.len()
        );
    }
    let tm = w.timings;
    println!(
        "result: responses={n} chunks={} outer={spec} chunks_s={chunks_s:.2} chunks_verify_s={chunks_verify_s:.3} \
         chunk_proof_bytes={chunk_bytes} wrap_s={wrap_s:.2} record_s={:.2} tapes_s={:.2} build_s={:.2} \
         witness_s={:.2} prove_s={:.2} wrap_verify_s={verify_s:.3} wrap_bytes={} public_words={} nu={} dense_m={}",
        chunks.len(),
        tm.record,
        tm.tapes,
        tm.build,
        tm.witness,
        tm.prove,
        wrap::proof_bytes(&w.proof),
        w.proof.public.len(),
        w.key.key.nu(),
        w.key.key.pcs.m,
    );
}
