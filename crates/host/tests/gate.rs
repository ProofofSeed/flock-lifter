// SPDX-License-Identifier: LGPL-3.0-or-later

//! The native Fiat-Shamir gate and the response check on inputs the acceptance runs do not reach:
//! challenge words that are not one of the three unit words, an expected output of another shape,
//! and AND messages shorter than the statement's.

use std::sync::Arc;

use flock_prover::field::F128;
use pofseed_flock_lift::lift::{LiftError, Statement, gate};
use pofseed_flock_lift_block::{
    native,
    program::{Program, WitnessError},
};
use pofseed_flock_lift_host::{
    HARDENED_OFFSET, bip32_vector_1,
    tamper::{oversize_and_msg, short_and_msg},
    vector_1_proof,
};
use pofseed_flock_lift_statement::{HardenedChildCircuit, S};
use zkboo::prover::proof::Response;

const BINDING: &[u8] = b"flock-lifter gate test binding";

struct Fixture {
    program: Arc<Program>,
    statement: Statement,
    words: Vec<Vec<F128>>,
    unopened: Vec<[u8; 32]>,
    proof: Vec<Response<S, S>>,
}

fn fixture(n: usize) -> Fixture {
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter gate test entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let circuit = statement.circuit();
    let words = proof
        .iter()
        .map(|r| native::io_words(&program, &circuit, &statement.expected_output, r).expect("replay"))
        .collect();
    let unopened = proof.iter().map(|r| *r.commitment_digest_unopened()).collect();
    return Fixture { program, statement, words, unopened, proof };
}

#[test]
fn the_gate_refuses_challenge_words_that_are_not_unit_words() {
    let f = fixture(6);
    gate(&f.program, &f.statement, &f.words, &f.unopened).expect("the genuine words pass");
    for i in [0, 5] {
        for bad in [F128::ZERO, F128::new(3, 0), F128::new(8, 0), F128::new(1, 1), F128::new(0, 1)] {
            let mut w = f.words.clone();
            w[i][0] = bad;
            assert!(
                matches!(gate(&f.program, &f.statement, &w, &f.unopened), Err(LiftError::Challenge(j)) if j == i),
                "challenge word {bad:?} at {i}"
            );
        }
        let mut w = f.words.clone();
        w[i][0] = F128::new(if f.words[i][0].lo == 1 { 2 } else { 1 }, 0);
        assert!(matches!(gate(&f.program, &f.statement, &w, &f.unopened), Err(LiftError::FiatShamir)), "another unit word at {i}");
    }
}

#[test]
fn the_gate_refuses_an_expected_output_of_another_shape() {
    let f = fixture(2);
    let mut longer = f.statement.clone();
    longer.expected_output.as_vec_mut::<u8>().push(1);
    assert!(matches!(gate(&f.program, &longer, &f.words, &f.unopened), Err(LiftError::Statement)));
    let mut shorter = f.statement.clone();
    shorter.expected_output.as_vec_mut::<u8>().pop();
    assert!(matches!(gate(&f.program, &shorter, &f.words, &f.unopened), Err(LiftError::Statement)));
    let mut fewer = f.unopened.clone();
    fewer.pop();
    assert!(matches!(gate(&f.program, &f.statement, &f.words, &fewer), Err(LiftError::Statement)));
}

#[test]
fn the_response_check_refuses_messages_of_another_length() {
    let f = fixture(1);
    f.program.check_response(&f.proof[0]).expect("a genuine response");
    assert!(matches!(f.program.check_response(&short_and_msg(&f.proof[0])), Err(WitnessError::AndMsgShape)));
    assert!(matches!(f.program.check_response(&oversize_and_msg(&f.proof[0])), Err(WitnessError::AndMsgShape)));
}
