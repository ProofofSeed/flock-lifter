// SPDX-License-Identifier: LGPL-3.0-or-later

//! Acceptance run for wrapped lifts: the reject matrix and a full-scale wrapped lift.
//!
//! The reject matrix is the direct route's, case for case, with the refuser of each:
//!
//! - R1 tampered proof (one AND-message bit flipped): the native Fiat-Shamir gate
//! - R2 wrong binding: the native Fiat-Shamir gate
//! - R3 wrong fingerprint expectation: `check_journal`
//! - R4 too few responses (8 < 219): `check_journal`
//! - R5 empty proof: the prover, which wraps at least one response
//! - R6 wrong statement expectation: `check_journal`
//! - R7 malformed response (oversized AND messages): the prover
//! - R8 wrong proof format expectation: `check_journal`
//!
//! and the cases the wrap's own structure opens:
//!
//! - W1 a tampered published word: the wrap's outer proof
//! - W2 a tampered unopened digest: the native Fiat-Shamir gate
//! - W3 two responses' published words swapped: the wrap's outer proof
//! - W4 a lift verified under another statement's tables: the structure proof
//! - W5 a truncated lift: the shape check
//! - W6 a tampered accumulated matrix claim: the wrap's outer proof
//! - W7 a tampered commitment: the wrap's outer proof
//! - W8 another lift's unopened digests: the native Fiat-Shamir gate
//! - W9 a key of another shape: the shape check
//!
//! It also checks that a key made by one lift verifies another lift of the same shape.
//!
//! Usage: `acceptance-wrap [rejects|full|both] [responses] [log inverse rate]` (default `both`, 219, 1).

use std::{env, sync::Arc, time::Instant};

use flock_prover::field::F128;
use pofseed_flock_lift::{
    lift::{LiftError, MAX_CHUNK, Statement},
    wrap::WrapError,
    wrapped::{WrappedLift, prove, verify},
};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_host::{
    HARDENED_OFFSET, bip32_vector_1, n_eps,
    tamper::{oversize_and_msg, tamper_and_msg},
    vector_1_proof,
};
use pofseed_flock_lift_statement::{
    H, HardenedChildCircuit, JournalCheckError, JournalExpectation, LiftJournal, REQUIRED_PROOF_FORMAT_ID,
    check_journal,
};
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
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

fn expect_refusal(name: &str, result: Result<LiftJournal, LiftError>, matches: impl Fn(&LiftError) -> bool) {
    match result {
        Ok(_) => panic!("{name}: the verifier ACCEPTED a lift it must refuse"),
        Err(e) if matches(&e) => println!("  {name}: refused ({}) ✓", brief(&e)),
        Err(e) => panic!("{name}: refused, but not by the named refuser: {e:?}"),
    }
}

fn brief(e: &LiftError) -> String {
    let s = format!("{e:?}");
    return if s.len() > 96 { format!("{}…", &s[..96]) } else { s };
}

fn expect_gate_refusal(name: &str, journal: &LiftJournal, exp: &JournalExpectation, expected: JournalCheckError) {
    match check_journal(journal, exp) {
        Err(e) if e == expected => println!("  {name}: refused by check_journal ({e:?}) ✓"),
        other => panic!("{name}: expected {expected:?}, got {other:?}"),
    }
}

fn key_one_shape(key: &pofseed_flock_lift::wrapped::WrappedKey) -> &pofseed_flock_lift::wrapped::WrappedKey {
    return key;
}

fn main() {
    let mode = env::args().nth(1).unwrap_or_else(|| "both".into());
    let full_n: usize = env::args().nth(2).map(|a| a.parse().expect("response count")).unwrap_or(n_eps(64));
    let rate: usize = env::args().nth(3).map(|a| a.parse().expect("log inverse rate")).unwrap_or(1);
    let full = matches!(mode.as_str(), "full" | "both");
    let rejects = matches!(mode.as_str(), "rejects" | "both");
    assert!(full || rejects, "usage: acceptance-wrap [rejects|full|both] [responses] [log inverse rate]");
    let outer = WhirOuter::new(4, rate, Regime::Johnson, 3, 22, 128).with_merkle(MerkleHash::Keccak);
    let (_, chain_code) = bip32_vector_1();
    let t = Instant::now();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    println!("block built in {:.2} s (k_log {})", t.elapsed().as_secs_f64(), program.geometry().k_log());
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
        let (key, lifted, _) = prove(&program, &statement, &proof, 4, &outer, None, rate).expect("control lift");
        let root = key.root.clone();
        let check = |s: &Statement, l: &WrappedLift| verify(&program, &key, s, l, &outer);
        let journal = check(&statement, &lifted).expect("control must verify");
        check_journal(&journal, &expectation(&statement, n as u32)).expect("control gate must pass");
        println!("  control (n=8, two chunks, matching expectation): accepted ✓");

        let mut tampered = proof.clone();
        tampered[3] = tamper_and_msg(&tampered[3]);
        let (_, lifted_r1, _) = prove(&program, &statement, &tampered, 4, &outer, Some(root.clone()), rate).expect("a tampered response still wraps");
        expect_refusal("R1 tampered proof", check(&statement, &lifted_r1), |e| matches!(e, LiftError::FiatShamir));

        let other_binding = Statement {
            binding: b"some other tx".to_vec(),
            ..statement.clone()
        };
        let (key_r2, lifted_r2, _) = prove(&program, &other_binding, &proof, 4, &outer, Some(root.clone()), rate).expect("lift under another binding");
        expect_refusal("R2 wrong binding", check(&other_binding, &lifted_r2), |e| matches!(e, LiftError::FiatShamir));

        let mut exp = expectation(&statement, n as u32);
        exp.fingerprint[0] ^= 1;
        expect_gate_refusal("R3 wrong fingerprint", &journal, &exp, JournalCheckError::FingerprintMismatch);

        let exp = expectation(&statement, n_eps(64) as u32);
        expect_gate_refusal("R4 too few responses", &journal, &exp, JournalCheckError::TooFewResponses);

        match prove(&program, &statement, &[], 4, &outer, Some(root.clone()), rate) {
            Err(e @ LiftError::Shape) => println!("  R5 empty proof: refused by the prover ({e:?}) ✓"),
            other => panic!("R5 empty proof: expected a shape refusal, got {:?}", other.map(|_| ())),
        }

        let mut exp = expectation(&statement, 0);
        exp.expected_output.as_vec_mut::<u8>()[0] ^= 1;
        expect_gate_refusal("R6 wrong statement", &journal, &exp, JournalCheckError::StatementMismatch);

        let mut malformed = proof.clone();
        malformed[5] = oversize_and_msg(&malformed[5]);
        match prove(&program, &statement, &malformed, 4, &outer, Some(root.clone()), rate) {
            Err(e @ LiftError::Witness(5, _)) => println!("  R7 malformed response: refused by the prover ({e:?}) ✓"),
            other => panic!("R7 malformed response: expected a witness refusal at response 5, got {:?}", other.map(|_| ())),
        }

        let mut exp = expectation(&statement, n as u32);
        exp.proof_format_id[0] ^= 1;
        expect_gate_refusal("R8 wrong proof format", &journal, &exp, JournalCheckError::ProofFormatMismatch);

        let outer_refuses = |e: &LiftError| matches!(e, LiftError::Wrap(WrapError::Outer(_)));
        let (at, _) = pofseed_flock_lift::wrap::words_at(&key.wrap, 1);
        let mut w1 = lifted.clone();
        w1.wrap.public[at + 2 * 16 + 1] += F128::ONE;
        expect_refusal("W1 tampered published word", check(&statement, &w1), outer_refuses);

        let mut w2 = lifted.clone();
        w2.unopened[2][0] ^= 1;
        expect_refusal("W2 tampered unopened digest", check(&statement, &w2), |e| matches!(e, LiftError::FiatShamir));

        let mut w3 = lifted.clone();
        for w in 0..16 {
            w3.wrap.public.swap(at + w, at + 16 + w);
        }
        expect_refusal("W3 swapped responses", check(&statement, &w3), outer_refuses);

        let other_index = Statement {
            index: HARDENED_OFFSET + 1,
            ..statement.clone()
        };
        let other_program = Program::new(&other_index.circuit());
        let other_key = pofseed_flock_lift::wrapped::WrappedKey {
            root: Arc::new(pofseed_flock_lift::root::RootKey::new(&other_program, &key_r2.wrap, rate)),
            ..key_r2
        };
        expect_refusal(
            "W4 another statement's tables",
            verify(&other_program, &other_key, &other_index, &lifted, &outer),
            |e| matches!(e, LiftError::Wrap(WrapError::Structure(_))),
        );

        let mut w5 = lifted.clone();
        w5.unopened.pop();
        expect_refusal("W5 truncated lift", check(&statement, &w5), |e| matches!(e, LiftError::Shape));

        let mut w6 = lifted.clone();
        let (acc, _, _) = key.wrap.acc[1];
        w6.wrap.public[acc + 3] += F128::ONE;
        expect_refusal("W6 tampered matrix claim", check(&statement, &w6), outer_refuses);

        let mut w7 = lifted.clone();
        w7.wrap.commitment.cap[0][0] ^= 1;
        expect_refusal("W7 tampered commitment", check(&statement, &w7), outer_refuses);

        let (_, output_b, proof_b) = vector_1_proof(n, b"another prover's entropy", BINDING);
        assert_eq!(output_b, output);
        let (_, lifted_b, _) = prove(&program, &statement, &proof_b, 4, &outer, Some(root.clone()), rate).expect("a second lift");
        let mut w8 = lifted.clone();
        w8.unopened = lifted_b.unopened.clone();
        expect_refusal("W8 another lift's unopened digests", check(&statement, &w8), |e| {
            matches!(e, LiftError::FiatShamir)
        });

        let (key_one, _, _) = prove(&program, &statement, &proof[..4], 4, &outer, None, rate).expect("a one-chunk lift");
        expect_refusal("W9 a key of another shape", verify(&program, &key_one, &statement, &lifted, &outer), |e| {
            matches!(e, LiftError::Shape)
        });

        verify(&program, &key_one_shape(&key), &statement, &lifted_b, &outer).expect("a key made by one lift verifies another");
        println!("  a key made by one lift verifies another of the same shape ✓");

        let mut s1 = lifted.clone();
        s1.structure.kernel_values[0] += F128::ONE;
        expect_refusal("S1 tampered structure proof", check(&statement, &s1), |e| {
            matches!(e, LiftError::Wrap(WrapError::Structure(_)))
        });
        let mut s2 = lifted.clone();
        s2.wrap.proof.wiring.gkr.s_sigma_eval += F128::ONE;
        expect_refusal("S2 tampered wiring evaluation", check(&statement, &s2), |e| matches!(e, LiftError::Wrap(_)));
        let mut s3 = lifted.clone();
        s3.wrap.proof.boolean.as_mut().expect("a Boolean class").lincheck.matrix_evals[0].1 += F128::ONE;
        expect_refusal("S3 tampered table evaluation", check(&statement, &s3), |e| matches!(e, LiftError::Wrap(_)));
        let mut s4 = lifted.clone();
        s4.structure = lifted_b.structure.clone();
        expect_refusal("S4 another lift's structure proof", check(&statement, &s4), |e| {
            matches!(e, LiftError::Wrap(WrapError::Structure(_)))
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
        let (key, lifted, tm) = prove(&program, &statement, &proof, MAX_CHUNK, &outer, None, rate).expect("full-scale lift");
        println!(
            "  wrapped lift in {:.2} s: chunks {:.2} s, wrap {:.2} s, tables committed in {:.2} s, structure proof {:.2} s",
            t.elapsed().as_secs_f64() - tm.key,
            tm.chunks,
            t.elapsed().as_secs_f64() - tm.chunks - tm.key - tm.structure,
            tm.key,
            tm.structure
        );
        println!(
            "  parts: wrap proof {} B, structure proof {} B, tables over 2^{} bytes",
            pofseed_flock_lift::wrap::proof_bytes(&lifted.wrap),
            bincode::serialize(&lifted.structure).expect("serialise").len(),
            key.root.structure.layout.n
        );
        println!("  wrapped lift: {} B", bincode::serialize(&lifted).expect("serialise").len());
        let t = Instant::now();
        let journal = verify(&program, &key, &statement, &lifted, &outer).expect("full-scale verify");
        println!("  verified in {:.3} s", t.elapsed().as_secs_f64());
        check_journal(&journal, &expectation(&statement, n_eps(64) as u32)).expect("relying-party gate");
        println!("  journal passes the relying-party gate: {} responses ✓", journal.num_responses);
    }
}
