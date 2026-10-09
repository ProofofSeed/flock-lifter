// SPDX-License-Identifier: LGPL-3.0-or-later

//! Acceptance run for the Flock lifter: the reject matrix and a full-scale lift.
//!
//! The reject matrix mirrors the SP1 lifter's, case for case, and names the refuser of each:
//!
//! - R1 tampered proof (one AND-message bit flipped): the native Fiat-Shamir gate
//! - R2 wrong binding: the native Fiat-Shamir gate
//! - R3 wrong fingerprint expectation: `check_journal`
//! - R4 too few responses (8 < 219): `check_journal`
//! - R5 empty proof: `check_journal`
//! - R6 wrong statement expectation: `check_journal`
//! - R7 malformed response (oversized AND messages): the prover, which cannot lay it into a block
//! - R8 wrong proof format expectation: `check_journal`
//!
//! and adds the cases the lift's own structure opens:
//!
//! - F1 a tampered published word: the chunk's Flock verification
//! - F2 a tampered unopened digest: the native Fiat-Shamir gate
//! - F3 two chunks swapped: the chunks' Flock verification
//! - F4 a lift verified under a statement the key is not for: the statement check
//! - F5 a truncated lift: the shape check
//! - F6 a tampered matrix proof: the matrix proof's verification
//! - F7 a missing matrix proof: the shape check
//! - F8 another lift's matrix proof: the matrix proof's verification
//! - F9 an expected output of another shape: the statement check
//!
//! Usage: `acceptance [rejects|full|both] [responses]` (default `both`, 219).

use std::{env, sync::Arc, time::Instant};

use flock_prover::field::F128;
use pofseed_flock_lift::lift::{LiftError, LiftKey, LiftedProof, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_host::{
    HARDENED_OFFSET, bip32_vector_1, n_eps,
    tamper::{oversize_and_msg, tamper_and_msg},
    vector_1_proof,
};
use pofseed_flock_lift_statement::{
    H, JournalCheckError, JournalExpectation, LiftJournal, REQUIRED_PROOF_FORMAT_ID, check_journal,
};
use zkboo_circuit_hash::hash_circuit;

const SEED_ENTROPY: &[u8] = b"flock-lifter acceptance entropy";
const BINDING: &[u8] = b"flock-lifter acceptance tx binding";

fn expectation(statement: &Statement, min_responses: u32) -> JournalExpectation {
    return JournalExpectation {
        fingerprint: hash_circuit::<_, H>(&statement.circuit()),
        chain_code: statement.chain_code.clone(),
        index: statement.index,
        expected_output: statement.expected_output.clone(),
        binding: statement.binding.clone(),
        min_responses,
        proof_format_id: REQUIRED_PROOF_FORMAT_ID,
    };
}

fn expect_lift_refusal(name: &str, result: Result<LiftJournal, LiftError>, matches: impl Fn(&LiftError) -> bool) {
    match result {
        Ok(_) => panic!("{name}: the verifier ACCEPTED a lift it must refuse"),
        Err(e) if matches(&e) => println!("  {name}: refused ({e:?}) ✓"),
        Err(e) => panic!("{name}: refused, but not by the named refuser: {e:?}"),
    }
}

fn expect_gate_refusal(name: &str, journal: &LiftJournal, exp: &JournalExpectation, expected: JournalCheckError) {
    match check_journal(journal, exp) {
        Err(e) if e == expected => println!("  {name}: refused by check_journal ({e:?}) ✓"),
        other => panic!("{name}: expected {expected:?}, got {other:?}"),
    }
}

fn main() {
    let mode = env::args().nth(1).unwrap_or_else(|| "both".into());
    let full_n: usize = env::args().nth(2).map(|a| a.parse().expect("response count")).unwrap_or(n_eps(64));
    let full = matches!(mode.as_str(), "full" | "both");
    let rejects = matches!(mode.as_str(), "rejects" | "both");
    assert!(full || rejects, "usage: acceptance [rejects|full|both] [responses]");
    let (_, chain_code) = bip32_vector_1();
    let t = Instant::now();
    let program = Arc::new(Program::new(&pofseed_flock_lift_statement::HardenedChildCircuit::public_only(
        chain_code.clone(),
        HARDENED_OFFSET,
    )));
    println!("block built in {:.2} s (k_log {})", t.elapsed().as_secs_f64(), program.geometry().k_log());
    let t = Instant::now();
    let key = LiftKey::new(program);
    let vk = key.verifying();
    println!("entry list committed in {:.2} s (2^{} entries)", t.elapsed().as_secs_f64(), key.matrix.log_len());
    if rejects {
        println!("── reject matrix (n=8) ──");
        let n = 8;
        let (_, output, proof) = vector_1_proof(n, SEED_ENTROPY, BINDING);
        let statement = Statement {
            chain_code: chain_code.clone(),
            index: HARDENED_OFFSET,
            expected_output: output.clone(),
            binding: BINDING.to_vec(),
        };
        let lifted = prove(&key, &statement, &proof, 4).expect("control lift");
        let journal = verify(&vk, &statement, &lifted).expect("control must verify");
        check_journal(&journal, &expectation(&statement, n as u32)).expect("control gate must pass");
        println!("  control (n=8, two chunks, matching expectation): accepted ✓");

        let mut tampered = proof.clone();
        tampered[3] = tamper_and_msg(&tampered[3]);
        let lifted_r1 = prove(&key, &statement, &tampered, 4).expect("a tampered response still lays into a block");
        expect_lift_refusal("R1 tampered proof", verify(&vk, &statement, &lifted_r1), |e| {
            matches!(e, LiftError::FiatShamir)
        });

        let other_binding = Statement {
            binding: b"some other tx".to_vec(),
            ..statement.clone()
        };
        let lifted_r2 = prove(&key, &other_binding, &proof, 4).expect("lift under another binding");
        expect_lift_refusal("R2 wrong binding", verify(&vk, &other_binding, &lifted_r2), |e| {
            matches!(e, LiftError::FiatShamir)
        });

        let mut exp = expectation(&statement, n as u32);
        exp.fingerprint[0] ^= 1;
        expect_gate_refusal("R3 wrong fingerprint", &journal, &exp, JournalCheckError::FingerprintMismatch);

        let exp = expectation(&statement, n_eps(64) as u32);
        expect_gate_refusal("R4 too few responses", &journal, &exp, JournalCheckError::TooFewResponses);

        let lifted_empty = prove(&key, &statement, &[], 4).expect("an empty lift");
        let empty_journal = verify(&vk, &statement, &lifted_empty).expect("the empty proof verifies by design");
        assert_eq!(empty_journal.num_responses, 0);
        expect_gate_refusal("R5 empty proof", &empty_journal, &expectation(&statement, 1), JournalCheckError::TooFewResponses);

        let mut exp = expectation(&statement, 0);
        exp.expected_output.as_vec_mut::<u8>()[0] ^= 1;
        expect_gate_refusal("R6 wrong statement", &journal, &exp, JournalCheckError::StatementMismatch);

        let mut malformed = proof.clone();
        malformed[5] = oversize_and_msg(&malformed[5]);
        match prove(&key, &statement, &malformed, 4) {
            Err(e @ LiftError::Witness(5, _)) => println!("  R7 malformed response: refused by the prover ({e:?}) ✓"),
            other => panic!("R7 malformed response: expected a witness refusal at response 5, got {:?}", other.map(|_| ())),
        }

        let mut exp = expectation(&statement, n as u32);
        exp.proof_format_id[0] ^= 1;
        expect_gate_refusal("R8 wrong proof format", &journal, &exp, JournalCheckError::ProofFormatMismatch);

        let mut f1 = lifted.clone();
        f1.words[6][1] += F128::ONE;
        expect_lift_refusal("F1 tampered published word", verify(&vk, &statement, &f1), |e| {
            matches!(e, LiftError::Chunk(1, _))
        });

        let mut f2: LiftedProof = lifted.clone();
        f2.unopened[2][0] ^= 1;
        expect_lift_refusal("F2 tampered unopened digest", verify(&vk, &statement, &f2), |e| {
            matches!(e, LiftError::FiatShamir)
        });

        let mut f3 = lifted.clone();
        f3.chunks.swap(0, 1);
        f3.words.rotate_left(4);
        expect_lift_refusal("F3 swapped chunks", verify(&vk, &statement, &f3), |e| matches!(e, LiftError::Chunk(0, _)));

        let other_index = Statement {
            index: HARDENED_OFFSET + 1,
            ..statement.clone()
        };
        expect_lift_refusal("F4 another statement", verify(&vk, &other_index, &lifted), |e| {
            matches!(e, LiftError::Statement)
        });

        let mut f5 = lifted.clone();
        f5.words.pop();
        expect_lift_refusal("F5 truncated lift", verify(&vk, &statement, &f5), |e| matches!(e, LiftError::Shape));

        let mut f6 = lifted.clone();
        f6.matrix.as_mut().expect("a matrix proof").counts[40] += F128::ONE;
        expect_lift_refusal("F6 tampered matrix proof", verify(&vk, &statement, &f6), |e| matches!(e, LiftError::Matrix(_)));

        let mut f7 = lifted.clone();
        f7.matrix = None;
        expect_lift_refusal("F7 missing matrix proof", verify(&vk, &statement, &f7), |e| matches!(e, LiftError::Shape));

        let mut f8 = lifted.clone();
        f8.matrix = lifted_r2.matrix.clone();
        expect_lift_refusal("F8 another lift's matrix proof", verify(&vk, &statement, &f8), |e| {
            matches!(e, LiftError::Matrix(_))
        });

        let mut other_shape = statement.clone();
        other_shape.expected_output.as_vec_mut::<u8>().push(1);
        expect_lift_refusal("F9 an expected output of another shape", verify(&vk, &other_shape, &lifted), |e| {
            matches!(e, LiftError::Statement)
        });
        println!("reject matrix: PASS");
        println!();
    }
    if full {
        let n = full_n;
        println!("── full-scale positive run (n={n}) ──");
        let t = Instant::now();
        let (_, output, proof) = vector_1_proof(n, SEED_ENTROPY, BINDING);
        println!("  zkboo proof of {n} responses in {:.2} s", t.elapsed().as_secs_f64());
        let statement = Statement {
            chain_code: chain_code.clone(),
            index: HARDENED_OFFSET,
            expected_output: output,
            binding: BINDING.to_vec(),
        };
        let t = Instant::now();
        let lifted = prove(&key, &statement, &proof, pofseed_flock_lift::lift::MAX_CHUNK).expect("full-scale lift");
        println!("  lifted in {:.2} s ({} chunks)", t.elapsed().as_secs_f64(), lifted.chunks.len());
        let bytes = bincode::serialize(&lifted).expect("serialise");
        println!("  lifted proof: {} B", bytes.len());
        let t = Instant::now();
        let journal = verify(&vk, &statement, &lifted).expect("full-scale verify");
        println!("  verified in {:.2} s", t.elapsed().as_secs_f64());
        check_journal(&journal, &expectation(&statement, n_eps(64) as u32)).expect("relying-party gate");
        println!("  journal passes the relying-party gate: {} responses ✓", journal.num_responses);
    }
}
