// SPDX-License-Identifier: LGPL-3.0-or-later

//! Times one full lift of a hardened-child ZKBoo proof: proof generation, lifting, verification
//! and the relying-party gate, with the lifted proof's serialised size.
//!
//! Usage: `lift-bench <responses> [chunk]` (chunk defaults to the largest).

use std::{env, sync::Arc, time::Instant};

use pofseed_flock_lift::lift::{LiftKey, MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{
    H, HardenedChildCircuit, JournalExpectation, REQUIRED_PROOF_FORMAT_ID, check_journal,
};
use zkboo_circuit_hash::hash_circuit;

fn main() {
    let n: usize = env::args().nth(1).expect("usage: lift-bench <responses> [chunk]").parse().expect("response count");
    let chunk: usize = env::args().nth(2).map(|a| a.parse().expect("chunk size")).unwrap_or(MAX_CHUNK);
    let threads = rayon::current_num_threads();
    println!("lift-bench: {n} responses, chunk {chunk}, {threads} threads");
    let t = Instant::now();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter bench entropy", b"flock-lifter bench binding");
    let zkboo_s = t.elapsed().as_secs_f64();
    let (_, chain_code) = bip32_vector_1();
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output.clone(),
        binding: b"flock-lifter bench binding".to_vec(),
    };
    let t = Instant::now();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    let block_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let key = LiftKey::new(program);
    let vk = key.verifying();
    let key_s = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let lifted = prove(&key, &statement, &proof, chunk).expect("lift");
    let prove_s = t.elapsed().as_secs_f64();
    let bytes = bincode::serialize(&lifted).expect("serialise").len();
    let chunk_bytes: usize = lifted.chunks.iter().map(|c| bincode::serialize(c).unwrap().len()).sum();
    let matrix_bytes = bincode::serialize(&lifted.matrix).unwrap().len();
    let t = Instant::now();
    let journal = verify(&vk, &statement, &lifted).expect("verify");
    let verify_s = t.elapsed().as_secs_f64();
    let expectation = JournalExpectation {
        fingerprint: hash_circuit::<_, H>(&statement.circuit()),
        chain_code,
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: statement.binding.clone(),
        min_responses: n as u32,
        proof_format_id: REQUIRED_PROOF_FORMAT_ID,
    };
    check_journal(&journal, &expectation).expect("relying-party gate");
    println!(
        "result: responses={n} chunks={} threads={threads} zkboo_s={zkboo_s:.2} block_s={block_s:.2} \
         key_s={key_s:.2} prove_s={prove_s:.2} verify_s={verify_s:.2} lifted_bytes={bytes} \
         chunk_proof_bytes={chunk_bytes} matrix_proof_bytes={matrix_bytes} gate=pass",
        lifted.chunks.len()
    );
}
