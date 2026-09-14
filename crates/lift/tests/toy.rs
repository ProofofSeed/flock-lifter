// SPDX-License-Identifier: LGPL-3.0-or-later

//! End-to-end Flock proofs over toy response blocks, through both chunk paths.

use std::{sync::Arc, time::Instant};

use flock_prover::field::F128;
use pofseed_flock_lift::{chunk, chunk_rm};
use pofseed_flock_lift_block::{native, program::Program, toy::Toy};
use pofseed_flock_lift_statement::{H, PS, PV, S};
use zkboo::{
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, proof::Response, views::OwnedFlexibleWordTriplePool},
};

const DOMAIN: &[u8] = b"pofseed-flock-lift-toy-test";

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

#[test]
fn toy_union_chunk_proves_and_verifies() {
    let (program, proof, publics) = fixture(8);
    let t = Instant::now();
    let c = chunk::prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    chunk::verify_chunk(&program, &publics, &c, DOMAIN).expect("an honest chunk verifies");
    println!("union toy chunk: prove {prove_ms:.0} ms, {} B", bincode::serialize(&c).unwrap().len());
    let mut tampered = publics.clone();
    tampered[7][2] += F128::ONE;
    assert!(chunk::verify_chunk(&program, &tampered, &c, DOMAIN).is_err(), "a tampered digest word is refused");
    assert!(chunk::verify_chunk(&program, &publics, &c, b"another domain").is_err(), "another domain is refused");
    let forged = chunk::prove_chunk(&program, &proof, &tampered, DOMAIN).expect("prove with forged publics");
    assert!(chunk::verify_chunk(&program, &tampered, &forged, DOMAIN).is_err(), "unbacked published words are refused");
}

#[test]
fn toy_row_major_chunk_proves_and_verifies() {
    let (program, proof, publics) = fixture(11);
    let t = Instant::now();
    let c = chunk_rm::prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    chunk_rm::verify_chunk(&program, &publics, &c, DOMAIN).expect("an honest chunk verifies");
    println!("row-major toy chunk: prove {prove_ms:.0} ms, {} B", bincode::serialize(&c).unwrap().len());
    let mut tampered = publics.clone();
    tampered[4][6] += F128::ONE;
    assert!(chunk_rm::verify_chunk(&program, &tampered, &c, DOMAIN).is_err(), "a tampered output-share word is refused");
    let mut challenge = publics.clone();
    challenge[0][0] = F128::new(3, 0);
    assert!(chunk_rm::verify_chunk(&program, &challenge, &c, DOMAIN).is_err(), "a tampered challenge word is refused");
    assert!(chunk_rm::verify_chunk(&program, &publics[..10], &c, DOMAIN).is_err(), "a dropped block is refused");
    assert!(chunk_rm::verify_chunk(&program, &publics, &c, b"another domain").is_err(), "another domain is refused");
    let forged = chunk_rm::prove_chunk(&program, &proof, &tampered, DOMAIN).expect("prove with forged publics");
    assert!(chunk_rm::verify_chunk(&program, &tampered, &forged, DOMAIN).is_err(), "unbacked published words are refused");
}
