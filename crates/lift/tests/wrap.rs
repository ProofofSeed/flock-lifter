// SPDX-License-Identifier: LGPL-3.0-or-later

//! Wraps of toy chunk proofs: acceptance through WHIR and through Ligerito, and refusals.

use std::{sync::Arc, time::Instant};

use flock_prover::{field::F128, pcs::OuterPcs, tower::HeadEnv};
use pofseed_flock_lift::{
    chunk_wrap::{self, ChunkProofWrap},
    root,
    wrap::{self, WrapError},
};
use pofseed_flock_lift_block::{native, program::Program, toy::Toy};
use pofseed_flock_lift_statement::{H, PS, PV, S};
use pofseed_flock_lift_whir::{outer::WhirOuter, params::MerkleHash};
use zkboo::{
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, proof::Response, views::OwnedFlexibleWordTriplePool},
};

fn fixture(responses: usize) -> (Arc<Program>, Vec<Response<S, S>>, Vec<Vec<F128>>) {
    let program = Arc::new(Program::new(&Toy));
    let output = exec::<_, OwnedFlexibleWordPool<usize>, _>(&Toy, ExecOptions::new());
    let proof = par_prove::<_, H, PS, PV, S, OwnedFlexibleWordTriplePool<usize>>(&Toy, responses, b"toy", b"");
    let publics = proof
        .iter()
        .map(|r| native::io_words(&program, &Toy, &output, r).expect("native replay"))
        .collect();
    return (program, proof, publics);
}

fn domain(i: usize) -> Vec<u8> {
    return format!("pofseed-flock-lift-wrap-test-{i}").into_bytes();
}

#[test]
fn toy_wrap_form_chunk_proves_and_verifies() {
    let (program, proof, publics) = fixture(11);
    let c = chunk_wrap::prove_chunk(&program, &proof, &publics, &domain(0)).expect("prove");
    chunk_wrap::verify_chunk(&program, &publics, &c, &domain(0)).expect("an honest chunk verifies");
    let mut tampered = publics.clone();
    tampered[4][6] += F128::ONE;
    assert!(chunk_wrap::verify_chunk(&program, &tampered, &c, &domain(0)).is_err(), "a tampered word");
    assert!(chunk_wrap::verify_chunk(&program, &publics[..10], &c, &domain(0)).is_err(), "a dropped block");
    assert!(chunk_wrap::verify_chunk(&program, &publics, &c, &domain(1)).is_err(), "another domain");
    let forged = chunk_wrap::prove_chunk(&program, &proof, &tampered, &domain(0)).expect("prove");
    assert!(chunk_wrap::verify_chunk(&program, &tampered, &forged, &domain(0)).is_err(), "unbacked words");
}

#[test]
fn toy_wrap_accepts_and_refuses() {
    let per = 1usize << chunk_wrap::row_log(&Program::new(&Toy), 1);
    let (program, proof, publics) = fixture(per + 3);
    let domains: Vec<Vec<u8>> = (0..2).map(domain).collect();
    let chunks: Vec<ChunkProofWrap> = proof
        .chunks(per)
        .zip(publics.chunks(per))
        .zip(&domains)
        .map(|((r, p), d)| chunk_wrap::prove_chunk(&program, r, p, d).expect("prove"))
        .collect();
    let parts: Vec<&[Vec<F128>]> = publics.chunks(per).collect();
    let whir = WhirOuter::standard().with_merkle(MerkleHash::Keccak);
    for outer in [Some(&whir as &dyn OuterPcs), None] {
        let t = Instant::now();
        let w = wrap::wrap(&program, &parts, &chunks, &domains, &HeadEnv::measuring(), outer).expect("wrap");
        println!(
            "wrap of {} chunks: {:.2} s, {} B, nu {}, timings {:?}",
            chunks.len(),
            t.elapsed().as_secs_f64(),
            wrap::proof_bytes(&w.proof),
            w.key.key.nu(),
            w.timings
        );
        wrap::verify_wrapped(&program, &parts, &w.key, &w.proof, outer).expect("an honest wrap verifies");
        let mut tampered = publics.clone();
        tampered[per + 1][3] += F128::ONE;
        let tparts: Vec<&[Vec<F128>]> = tampered.chunks(per).collect();
        assert!(
            matches!(wrap::verify_wrapped(&program, &tparts, &w.key, &w.proof, outer), Err(WrapError::Words)),
            "a tampered published word"
        );
        let swapped = [parts[1], parts[0]];
        assert!(wrap::verify_wrapped(&program, &swapped, &w.key, &w.proof, outer).is_err(), "swapped chunks");
        let mut p = w.proof.clone();
        let (at, _, _) = w.key.acc[0];
        p.public[at] += F128::ONE;
        assert!(wrap::verify_wrapped(&program, &parts, &w.key, &p, outer).is_err(), "a tampered accumulator");
        let mut p = w.proof.clone();
        p.commitment.cap[0][0] ^= 1;
        assert!(wrap::verify_wrapped(&program, &parts, &w.key, &p, outer).is_err(), "a tampered commitment");
    }
    let mut forged = chunks.clone();
    forged[1].lincheck.z_partial[5] += F128::ONE;
    assert!(
        matches!(
            wrap::wrap(&program, &parts, &forged, &domains, &HeadEnv::measuring(), None),
            Err(WrapError::Chunk(1, _))
        ),
        "a chunk that does not verify is not wrapped"
    );
}

/// Element-table matrix evaluations shifted along the lincheck's one recombination equation are
/// refused by Flock's circuit verifier and, independently, by the claims pass.
#[test]
fn shifted_element_matrix_evaluations_are_refused() {
    let per = 1usize << chunk_wrap::row_log(&Program::new(&Toy), 1);
    let (program, proof, publics) = fixture(per);
    let domains = vec![domain(0)];
    let chunks = vec![chunk_wrap::prove_chunk(&program, &proof, &publics, &domains[0]).expect("prove")];
    let parts: Vec<&[Vec<F128>]> = vec![&publics[..]];
    let whir = WhirOuter::standard().with_merkle(MerkleHash::Keccak);
    let outer = Some(&whir as &dyn OuterPcs);
    let w = wrap::wrap(&program, &parts, &chunks, &domains, &HeadEnv::measuring(), outer).expect("wrap");
    wrap::verify_wrapped(&program, &parts, &w.key, &w.proof, outer).expect("an honest wrap verifies");
    let (work, _) = w
        .key
        .key
        .verify_deferred(&w.proof, outer, &mut wrap::outer_transcript(&w.proof.public))
        .expect("the deferred verification");
    let alpha = work.element.expect("an element class").alpha;
    let mut forged = w.proof.clone();
    let evals = &mut forged.proof.element.as_mut().expect("an element proof").lincheck.matrix_evals;
    evals[0].0 += alpha;
    evals[0].1 += F128::ONE;
    assert!(
        w.key.key.verify_on(&forged, outer, &mut wrap::outer_transcript(&forged.public)).is_err(),
        "Flock's own verifier refuses the shifted evaluations"
    );
    let table_of = vec![0; w.key.key.shape.registry.num_boolean()];
    assert!(
        matches!(root::outer_claims(&w.key, &table_of, &forged, outer), Err(WrapError::Element)),
        "the claims pass refuses evaluations that are not the tables'"
    );
    assert!(
        matches!(wrap::verify_wrapped(&program, &parts, &w.key, &forged, outer), Err(WrapError::Outer(_))),
        "the wrap verifier refuses them"
    );
}

#[test]
fn toy_wrap_verifies_against_committed_tables() {
    let per = 1usize << chunk_wrap::row_log(&Program::new(&Toy), 1);
    let (program, proof, publics) = fixture(per + 2);
    let domains: Vec<Vec<u8>> = (0..2).map(domain).collect();
    let chunks: Vec<ChunkProofWrap> = proof
        .chunks(per)
        .zip(publics.chunks(per))
        .zip(&domains)
        .map(|((r, p), d)| chunk_wrap::prove_chunk(&program, r, p, d).expect("prove"))
        .collect();
    let parts: Vec<&[Vec<F128>]> = publics.chunks(per).collect();
    let whir = WhirOuter::standard().with_merkle(MerkleHash::Keccak);
    let outer = Some(&whir as &dyn OuterPcs);
    let w = wrap::wrap(&program, &parts, &chunks, &domains, &HeadEnv::measuring(), outer).expect("wrap");
    let t = Instant::now();
    let key = root::RootKey::new(&program, &w.key, 1);
    println!("tables committed over 2^{} bytes in {:.2} s", key.structure.layout.n, t.elapsed().as_secs_f64());
    let t = Instant::now();
    let structure = root::prove_structure(&key, &w.key, &w.proof, outer).expect("the structure proof");
    println!("structure proof in {:.2} s, {} B", t.elapsed().as_secs_f64(), bincode::serialize(&structure).unwrap().len());
    let vk = key.verifying();
    root::verify_root(&vk, &w.key, &w.proof, &structure, outer).expect("an honest wrap verifies against the commitment");

    let mut p = w.proof.clone();
    let (at, _, _) = w.key.acc[0];
    p.public[at] += F128::ONE;
    assert!(root::verify_root(&vk, &w.key, &p, &structure, outer).is_err(), "a tampered accumulator");
    let mut s = structure.clone();
    s.kernel_values[1] += F128::ONE;
    assert!(root::verify_root(&vk, &w.key, &w.proof, &s, outer).is_err(), "a tampered structure proof");
    let mut forged = w.proof.clone();
    forged.proof.wiring.gkr.s_sigma_eval += F128::ONE;
    assert!(root::verify_root(&vk, &w.key, &forged, &structure, outer).is_err(), "a tampered wiring evaluation");
    let mut forged = w.proof.clone();
    forged.proof.boolean.as_mut().expect("a Boolean class").lincheck.matrix_evals[2].0 += F128::ONE;
    assert!(root::verify_root(&vk, &w.key, &forged, &structure, outer).is_err(), "a tampered table evaluation");

    // Another statement's block, same wrap circuit: the commitment differs and the proof is refused.
    let mut other = key.verifying();
    other.structure.commitment.cap[1][3] ^= 1;
    assert!(
        matches!(root::verify_root(&other, &w.key, &w.proof, &structure, outer), Err(WrapError::Structure(_))),
        "another commitment"
    );
}
