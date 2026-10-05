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
    if env::var_os("POFSEED_SHAPE").is_some() {
        use flock_prover::union::UnionInstance;
        let shape = &w.key.key.shape;
        let reg = &shape.registry;
        let union = UnionInstance::new(reg, shape.counts.clone());
        let cells = shape.circuit.cells();
        println!(
            "shape: nu {} M {} M_bool {} M_elem {} dense_m {} col_log {} mu {} c_bits {} gate slots {} public slots {} public words {}",
            reg.nu(),
            reg.m_total(),
            reg.m_bool(),
            reg.m_elem(),
            union.dense_m(),
            union.col_log(),
            cells.mu(),
            cells.c_bits(),
            cells.num_gate_slots(),
            cells.num_public_slots(),
            shape.circuit.num_public(),
        );
        for (i, ((ty, slot), n)) in reg.types().iter().zip(reg.slots()).zip(&shape.counts).enumerate() {
            println!(
                "  type {i}: element {} k_log {} useful {} pin {:?} schema {} prefix {:#x}/{} count {} nnz a {} b {}",
                ty.is_element(),
                ty.k_log,
                ty.useful_bits,
                ty.const_pin,
                ty.io_schema.len(),
                slot.prefix,
                slot.prefix_bits,
                n,
                ty.a_0.rows.iter().map(Vec::len).sum::<usize>(),
                ty.b_0.rows.iter().map(Vec::len).sum::<usize>(),
            );
        }
        for (i, ty) in reg.boolean_types().iter().enumerate() {
            for (side, m) in [("a", &ty.a_0), ("b", &ty.b_0)] {
                let mut diag: Vec<(i64, usize)> = Vec::new();
                for (r, row) in m.rows.iter().enumerate() {
                    for &c in row {
                        diag.push((c as i64 - r as i64, r));
                    }
                }
                diag.sort_unstable();
                let mut runs = 0usize;
                let mut aligned = 0usize;
                let mut prev: Option<(i64, usize)> = None;
                for &(d, r) in &diag {
                    let cont = prev == Some((d, r.wrapping_sub(1)));
                    if !cont {
                        runs += 1;
                    }
                    if !cont || r % 32 == 0 {
                        aligned += 1;
                    }
                    prev = Some((d, r));
                }
                let mut cyc: Vec<(usize, usize, usize, usize)> = Vec::new();
                for (r, row) in m.rows.iter().enumerate() {
                    for &c in row {
                        cyc.push((r / 32, c / 32, (c % 32 + 32 - r % 32) % 32, r % 32));
                    }
                }
                cyc.sort_unstable();
                let mut cyc_runs = 0usize;
                let mut prev: Option<(usize, usize, usize, usize)> = None;
                for &(a, b, u, t) in &cyc {
                    if prev != Some((a, b, u, t.wrapping_sub(1))) {
                        cyc_runs += 1;
                    }
                    prev = Some((a, b, u, t));
                }
                println!(
                    "  type {i} {side}: nnz {}, diagonal runs {runs}, word-aligned diagonal runs {aligned}, cyclic-32 runs {cyc_runs}",
                    diag.len()
                );
            }
        }
        let live: usize = shape.circuit.live_mask().counts.iter().sum();
        let heights = union.jagged_heights();
        println!(
            "  live cells {live}, layout columns {} used {}, fixed publics {}",
            heights.len(),
            heights.iter().filter(|&&h| h > 0).count(),
            shape.circuit.fixed_public().iter().filter(|f| f.is_some()).count()
        );
    }
    if env::var_os("POFSEED_LAYOUT").is_some() {
        use flock_prover::union::UnionInstance;
        let shape = &w.key.key.shape;
        let reg = &shape.registry;
        let union = UnionInstance::new(reg, shape.counts.clone());
        println!("layout: tails {:?}", w.key.tails);
        println!("layout: acc {:?} block {}", w.key.acc, w.key.block);
        println!("layout: pcs {:?}", w.key.key.pcs);
        let fixed = shape.circuit.fixed_public();
        let mut runs: Vec<(usize, usize)> = Vec::new();
        for (i, f) in fixed.iter().enumerate() {
            if f.is_some() {
                match runs.last_mut() {
                    Some((s, l)) if *s + *l == i => *l += 1,
                    _ => runs.push((i, 1)),
                }
            }
        }
        println!("layout: fixed public runs {:?}", runs);
        for (i, ty) in reg.element_types().iter().enumerate() {
            let e = ty.element_type().expect("an element type");
            let nnz = |m: &flock_prover::element_r1cs::SparseF128Matrix| {
                let all: usize = m.rows.iter().map(Vec::len).sum();
                let units: usize = m.rows.iter().flatten().filter(|(_, c)| *c == F128::ONE).count();
                let rows = m.rows.iter().filter(|r| !r.is_empty()).count();
                (all, units, rows)
            };
            println!(
                "layout: element {i}: kappa {} width {} k {} a {:?} b {:?} a_const {} b_const {}",
                e.kappa(),
                e.width(),
                e.k(),
                nnz(e.a_0()),
                nnz(e.b_0()),
                e.a_const().iter().filter(|c| !c.is_zero()).count(),
                e.b_const().iter().filter(|c| !c.is_zero()).count(),
            );
        }
        let heights = union.jagged_heights();
        let mut bounds: Vec<(u64, u64, usize)> = Vec::new();
        let mut t = 0u64;
        for &h in &heights {
            match bounds.last_mut() {
                Some((c, d, run)) if *c == t && *d == t + h => *run += 1,
                _ => bounds.push((t, t + h, 1)),
            }
            t += h;
        }
        println!("layout: boundary runs {} (zero-height {}), area {t}", bounds.len(), bounds.iter().filter(|b| b.0 == b.1).count());
        println!("layout: slots element prefix coords {:?}", union.element_prefix_coords().len());
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
