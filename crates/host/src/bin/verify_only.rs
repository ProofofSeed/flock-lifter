// SPDX-License-Identifier: LGPL-3.0-or-later

//! Splits a lift across two processes so the verifier's own time and memory can be read without
//! the prover's, which dwarfs both.
//!
//! Usage: `verify-only prove <responses> <file>` then `verify-only check <responses> <file>`.

use std::{env, fs, sync::Arc, time::Instant};

use pofseed_flock_lift::lift::{LiftedProof, MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{
    H, HardenedChildCircuit, JournalExpectation, REQUIRED_PROOF_FORMAT_ID, check_journal,
};
use zkboo_circuit_hash::hash_circuit;

const BINDING: &[u8] = b"flock-lifter verify-only binding";

fn main() {
    let mode = env::args().nth(1).expect("usage: verify-only <prove|check> <responses> <file>");
    let n: usize = env::args().nth(2).expect("response count").parse().expect("response count");
    let file = env::args().nth(3).expect("file");
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter verify-only entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output.clone(),
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    match mode.as_str() {
        "prove" => {
            let lifted = prove(&program, &statement, &proof, MAX_CHUNK).expect("lift");
            fs::write(&file, bincode::serialize(&lifted).expect("serialise")).expect("write");
            println!("wrote {file}");
        }
        "check" => {
            let bytes = fs::read(&file).expect("read");
            let lifted: LiftedProof = bincode::deserialize(&bytes).expect("deserialise");
            let t = Instant::now();
            let journal = verify(&program, &statement, &lifted).expect("verify");
            let verify_s = t.elapsed().as_secs_f64();
            let expectation = JournalExpectation {
                fingerprint: hash_circuit::<_, H>(&statement.circuit()),
                chain_code,
                index: HARDENED_OFFSET,
                expected_output: output,
                binding: BINDING.to_vec(),
                min_responses: n as u32,
                proof_format_id: REQUIRED_PROOF_FORMAT_ID,
            };
            check_journal(&journal, &expectation).expect("relying-party gate");
            println!("result: responses={n} chunks={} verify_s={verify_s:.3} gate=pass", lifted.chunks.len());
        }
        other => panic!("unknown mode {other}"),
    }
}
