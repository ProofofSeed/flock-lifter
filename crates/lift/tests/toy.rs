// SPDX-License-Identifier: LGPL-3.0-or-later

//! End-to-end Flock proofs over toy response blocks.

use std::{sync::Arc, time::Instant};

use flock_prover::field::F128;
use pofseed_flock_lift::chunk::{prove_chunk, verify_chunk};
use pofseed_flock_lift_block::{native, program::Program, toy::Toy};
use pofseed_flock_lift_statement::{H, PS, PV, S};
use zkboo::{
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, views::OwnedFlexibleWordTriplePool},
};

const DOMAIN: &[u8] = b"pofseed-flock-lift-toy-test";

#[test]
fn toy_chunk_proves_and_verifies() {
    let program = Arc::new(Program::new(&Toy));
    let output = exec::<_, OwnedFlexibleWordPool<usize>, _>(&Toy, ExecOptions::new());
    let proof = par_prove::<_, H, PS, PV, S, OwnedFlexibleWordTriplePool<usize>>(&Toy, 11, b"toy", b"");
    let publics: Vec<Vec<F128>> = proof
        .iter()
        .map(|r| native::io_words(&program, &Toy, &output, r).expect("native replay"))
        .collect();
    let t = Instant::now();
    let chunk = prove_chunk(&program, &proof, &publics, DOMAIN).expect("prove");
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    let t = Instant::now();
    verify_chunk(&program, &publics, &chunk, DOMAIN).expect("an honest chunk verifies");
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;
    let size = bincode::serialize(&chunk.proof).unwrap().len() + bincode::serialize(&chunk.commitment).unwrap().len();
    println!("toy chunk of {} responses: prove {prove_ms:.0} ms, verify {verify_ms:.0} ms, {size} B", proof.len());
    let mut tampered = publics.clone();
    tampered[7][2] += F128::ONE;
    assert!(verify_chunk(&program, &tampered, &chunk, DOMAIN).is_err(), "a tampered digest word is refused");
    assert!(verify_chunk(&program, &publics, &chunk, b"another domain").is_err(), "another domain is refused");
    let forged = prove_chunk(&program, &proof, &tampered, DOMAIN).expect("prove with forged publics");
    assert!(verify_chunk(&program, &tampered, &forged, DOMAIN).is_err(), "published words the witness does not carry are refused");
}
