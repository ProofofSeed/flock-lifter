// SPDX-License-Identifier: LGPL-3.0-or-later

//! The mirror verifier accepts what the lifter's verifier accepts, closes the matrix claim with
//! the block's structured discharge, and refuses tampered calldata.

use std::sync::Arc;

use pofseed_flock_lift::lift::{LiftKey, MAX_CHUNK, Statement, domain, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{calldata::encode_chunk, mirror::verify_chunk};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;

const BINDING: &[u8] = b"flock-lifter evm mirror binding";

#[test]
fn mirror_accepts_a_genuine_chunk_and_refuses_tampering() {
    let n = 8;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter evm mirror entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let lifted = prove(&LiftKey::new(program.clone()), &statement, &proof, MAX_CHUNK).expect("lift");
    verify(&LiftKey::new(program.clone()).verifying(), &statement, &lifted).expect("lifter verifies");
    let dom = domain(&statement.digest(n, MAX_CHUNK as u32), 0);
    let data = encode_chunk(&lifted.chunks[0], n);
    eprintln!("chunk calldata: {} bytes", data.len());
    let claim = verify_chunk(&program, &lifted.words, &dom, &data).expect("mirror verifies");
    let comb = program.comb_partial(claim.alpha, claim.beta, &claim.skip_weights, &claim.x_inner_rest, &claim.r_inner_rest);
    assert!(claim.closes(&comb), "the discharge closes the matrix claim");
    for at in (0..data.len()).step_by(data.len() / 97 + 1) {
        let mut bad = data.clone();
        bad[at] ^= 0x10;
        let refused = match verify_chunk(&program, &lifted.words, &dom, &bad) {
            Err(_) => true,
            Ok(c) => !c.closes(&program.comb_partial(c.alpha, c.beta, &c.skip_weights, &c.x_inner_rest, &c.r_inner_rest)),
        };
        assert!(refused, "a flipped byte at {at} was accepted");
    }
    let mut words = lifted.words.clone();
    words[3][2].lo ^= 1;
    assert!(verify_chunk(&program, &words, &dom, &data).is_err(), "a changed published word was accepted");
}
