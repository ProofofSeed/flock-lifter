// SPDX-License-Identifier: LGPL-3.0-or-later

//! A lift verifies in transactions under mainnet's gas cap, from contracts under its code-size
//! limit, with the same matrix claims the single-call verifier returns; a matrix session only
//! starts on claims a lift session recorded, and tampering is refused.

use std::sync::Arc;

use pofseed_flock_lift::lift::{LiftKey, Statement, prove};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::{encode_lift, encode_matrix},
    evm::{Evm, TX_CAP, artifact, encode},
    staged::{self, stage_name},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit};
use revm::primitives::{U256, keccak256};
use zkboo_circuit_hash::hash_circuit;

const BINDING: &[u8] = b"flock-lifter staged binding";

fn word(out: &[u8], at: usize) -> U256 {
    return U256::from_be_slice(&out[at..at + 32]);
}

#[test]
fn a_lift_verifies_in_capped_transactions() {
    let n = 8;
    let chunk = 4;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter staged entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    let key = LiftKey::new(program.clone());
    let vk = key.verifying();
    let lifted = prove(&key, &statement, &proof, chunk).expect("lift");
    let digest = statement.digest(n, chunk as u32);
    let lift_data = encode_lift(&lifted);
    let matrix_data = encode_matrix(lifted.matrix.as_ref().expect("matrix proof"), &vk.matrix);
    let fingerprint = hash_circuit::<_, H>(&statement.circuit());
    let y = &statement.expected_output;
    let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
    let output_bytes = y.as_bytes();

    let mut reference = Evm::new();
    let mut code = artifact("FlockLift.sol", "FlockLift");
    code.extend_from_slice(&fingerprint);
    code.extend_from_slice(&chain_code);
    code.extend_from_slice(&U256::from(HARDENED_OFFSET).to_be_bytes::<32>());
    code.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
    code.extend_from_slice(&U256::ZERO.to_be_bytes::<32>());
    let (at, _) = reference.deploy(code);
    let out = reference.call(
        at,
        encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&output_bytes).uint(counts).bytes(BINDING).bytes(&lift_data)),
    );
    assert!(out.success, "the single-call verifier refused");
    let claims: Vec<U256> = (0..word(&out.output, 32).to::<usize>()).map(|i| word(&out.output, 64 + 32 * i)).collect();

    let mut evm = Evm::mainnet();
    let dep = staged::deploy(&mut evm, &fingerprint, &chain_code, HARDENED_OFFSET, n, &program, &vk.matrix, false);
    for (name, size, gas) in &dep.contracts {
        eprintln!("{name}: {size} bytes, deployed for {gas} gas");
    }
    let salt = U256::from(1);

    let (opened, state) = staged::start_lift(&mut evm, dep.sessions, U256::from(9), &output_bytes, counts, BINDING, n, chunk);
    assert!(opened.success, "startLift refused");
    let mut stale = state.clone();
    stale[32 + 32 + 96 + 32 + 59 * 32 + 31] ^= 1;
    let nio = lifted.words[0].len();
    let region = &lift_data[..8 + 16 * nio * n + 32 * n];
    assert!(!staged::advance(&mut evm, dep.sessions, U256::from(9), &stale, 1, region).success, "a state other than the recorded one");
    assert!(!staged::advance(&mut evm, dep.sessions, U256::from(10), &state, 1, region).success, "an unopened session");
    assert!(staged::advance(&mut evm, dep.sessions, U256::from(9), &state, 1, region).success, "the recorded state");

    let mut bad = lift_data.clone();
    let at = bad.len() - 5000;
    bad[at] ^= 1;
    let refused = staged::lift(&mut evm, dep.sessions, U256::from(7), &output_bytes, counts, BINDING, &bad, n, chunk);
    let refusal = refused.err().expect("a tampered lift was accepted");
    eprintln!("tampered lift refused at stage {} ({})", refusal.stage, stage_name(refusal.stage));

    let session = staged::lift(&mut evm, dep.sessions, salt, &output_bytes, counts, BINDING, &lift_data, n, chunk)
        .expect("the staged lift refused");
    let (recorded, _) = staged::recorded(&mut evm, dep.sessions, &digest);
    let packed: Vec<u8> = claims.iter().flat_map(|c| c.to_be_bytes::<32>()).collect();
    assert_eq!(recorded, U256::from_be_bytes(keccak256(&packed).0), "recorded claims differ from the single call's");

    let mut forged = claims.clone();
    forged[3] ^= U256::from(1);
    assert!(!staged::start_matrix(&mut evm, dep.sessions, U256::from(2), &digest, &forged).success, "forged claims");
    let mut other = digest;
    other[0] ^= 1;
    assert!(!staged::start_matrix(&mut evm, dep.sessions, U256::from(3), &other, &claims).success, "unrecorded digest");

    let mut bad = matrix_data.clone();
    let at = bad.len() / 3;
    bad[at] ^= 4;
    let refusal = staged::matrix(&mut evm, dep.sessions, U256::from(8), &digest, &claims, &bad)
        .err()
        .expect("a tampered matrix proof was accepted");
    eprintln!("tampered matrix proof refused at stage {} ({})", refusal.stage, stage_name(refusal.stage));

    let msession = staged::matrix(&mut evm, dep.sessions, U256::from(4), &digest, &claims, &matrix_data)
        .expect("the staged matrix verification refused");
    let (_, accepted) = staged::recorded(&mut evm, dep.sessions, &digest);
    assert!(accepted, "not accepted");

    for (label, s) in [("lift", &session), ("matrix", &msession)] {
        let total: u64 = s.txs.iter().map(|t| t.gas).sum();
        let max = s.txs.iter().map(|t| t.gas).max().unwrap();
        eprintln!("{label}: {} transactions, {total} gas, largest {max}", s.txs.len());
        assert!(max <= TX_CAP);
    }
}
