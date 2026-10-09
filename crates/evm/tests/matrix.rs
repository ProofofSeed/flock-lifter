// SPDX-License-Identifier: LGPL-3.0-or-later

//! The matrix contract accepts a genuine lift's matrix proof exactly as the mirror does, and
//! refuses tampering with the proof, the claims and the pinned commitment.

use std::sync::Arc;

use pofseed_flock_lift::{
    chunk_rm::verify_chunk_deferred,
    lift::{LiftKey, Statement, domain, matrix_domain, prove},
};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::{encode_lift, encode_matrix},
    committed::{deploy_matrix, verify},
    evm::{Evm, artifact, encode},
    mirror::verify_matrix,
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use revm::primitives::U256;

const BINDING: &[u8] = b"flock-lifter evm matrix binding";

fn word(out: &[u8], at: usize) -> U256 {
    return U256::from_be_slice(&out[at..at + 32]);
}

#[test]
fn matrix_contract_matches_the_mirror_and_refuses_tampering() {
    let n = 8;
    let chunk = 4;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter evm matrix entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let key = LiftKey::new(program.clone());
    let vk = key.verifying();
    let lifted = prove(&key, &statement, &proof, chunk).expect("lift");
    let digest = statement.digest(n, chunk as u32);
    let claims: Vec<_> = lifted
        .chunks
        .iter()
        .zip(lifted.words.chunks(chunk))
        .enumerate()
        .map(|(i, (c, w))| verify_chunk_deferred(&program, w, c, &domain(&digest, i)).expect("chunk"))
        .collect();
    let matrix = lifted.matrix.as_ref().expect("a matrix proof");
    let data = encode_matrix(matrix, &vk.matrix);
    let mdom = matrix_domain(&digest);
    verify_matrix(vk.matrix.log_len, &vk.matrix.commitment.cap, &claims, &mdom, &data).expect("mirror verifies");

    let mut evm = Evm::new();
    let mut code = artifact("FlockLift.sol", "FlockLift");
    code.extend_from_slice(&zkboo_circuit_hash::hash_circuit::<_, pofseed_flock_lift_statement::H>(&statement.circuit()));
    code.extend_from_slice(&statement.chain_code);
    code.extend_from_slice(&U256::from(statement.index).to_be_bytes::<32>());
    code.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
    let y = &statement.expected_output;
    let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
    code.extend_from_slice(&counts.to_be_bytes::<32>());
    code.extend_from_slice(&U256::ZERO.to_be_bytes::<32>());
    let (lift, _) = evm.deploy(code);
    let out = evm.call(
        lift,
        encode("verify(bytes,uint256,bytes,bytes)", |a| {
            a.bytes(&y.as_bytes()).uint(counts).bytes(BINDING).bytes(&encode_lift(&lifted))
        }),
    );
    assert!(out.success, "lift refused");
    let packed: Vec<U256> = (0..word(&out.output, 32).to::<usize>()).map(|i| word(&out.output, 64 + 32 * i)).collect();
    let (at, deploy_gas) = deploy_matrix(&mut evm, &program, &vk.matrix, false);
    let good = verify(&mut evm, at, &packed, &digest, &data);
    assert!(good.success, "matrix contract refused: {}", hex::encode(&good.output));
    let mut last = 0u64;
    for (topics, body) in &good.logs {
        let id = U256::from_be_bytes(topics[1]).to::<u64>();
        let left = U256::from_be_slice(&body[..32]).to::<u64>();
        if last > 0 {
            eprintln!("phase {id}: {} gas", last - left);
        }
        last = left;
    }
    eprintln!(
        "matrix contract: deployment {deploy_gas} gas; {} gas in all, {} of it execution, calldata {} bytes",
        good.gas,
        good.execution(),
        data.len()
    );

    let cap_bytes = 32 * vk.matrix.commitment.cap.len();
    for at_byte in [5, cap_bytes + 3, cap_bytes + 8 + 40, data.len() / 4, data.len() / 3, data.len() / 2, data.len() - 30] {
        let mut bad = data.clone();
        bad[at_byte] ^= 0x04;
        let out = verify(&mut evm, at, &packed, &digest, &bad);
        assert!(!out.success, "byte {at_byte}: the contract accepted a tampered proof");
        assert!(
            verify_matrix(vk.matrix.log_len, &vk.matrix.commitment.cap, &claims, &mdom, &bad).is_err(),
            "byte {at_byte}: the mirror accepted a tampered proof"
        );
    }
    let mut other = digest;
    other[0] ^= 1;
    assert!(!verify(&mut evm, at, &packed, &other, &data).success, "another digest");
    let mut wrong = packed.clone();
    wrong[112 + 3] ^= U256::from(1);
    assert!(!verify(&mut evm, at, &wrong, &digest, &data).success, "a changed running claim");
    let mut wrong_beta = packed.clone();
    wrong_beta[1] ^= U256::from(1);
    assert!(!verify(&mut evm, at, &wrong_beta, &digest, &data).success, "a changed constant-wire pin");
    let mut wrong_alpha = packed.clone();
    wrong_alpha[112] ^= U256::from(1);
    assert!(!verify(&mut evm, at, &wrong_alpha, &digest, &data).success, "a changed A-side challenge");
    let mut other_key = vk.matrix.clone();
    other_key.commitment.cap[0][0] ^= 1;
    let (elsewhere, _) = deploy_matrix(&mut evm, &program, &other_key, false);
    assert!(!verify(&mut evm, elsewhere, &packed, &digest, &data).success, "another pinned commitment");
}
