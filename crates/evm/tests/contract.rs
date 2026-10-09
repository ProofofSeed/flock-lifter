// SPDX-License-Identifier: LGPL-3.0-or-later

//! The contract verifies a genuine chunk exactly as the mirror does, and refuses tampering.

use std::sync::Arc;

use flock_prover::field::F128;
use pofseed_flock_lift::lift::{LiftKey, MAX_CHUNK, Statement, domain, prove};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::{Writer, encode_chunk},
    evm::{Evm, artifact, encode},
    mirror::{MatrixClaim, verify_chunk},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use revm::primitives::U256;

const BINDING: &[u8] = b"flock-lifter evm contract binding";

fn u(v: F128) -> U256 {
    return U256::from(((v.hi as u128) << 64) | v.lo as u128);
}

fn word(out: &[u8], at: usize) -> U256 {
    return U256::from_be_slice(&out[at..at + 32]);
}

fn array(out: &[u8], base: usize, head: usize) -> Vec<U256> {
    let at = base + word(out, head).to::<usize>();
    let n = word(out, at).to::<usize>();
    return (0..n).map(|i| word(out, at + 32 + 32 * i)).collect();
}

fn assert_claim(out: &[u8], mc: &MatrixClaim) {
    let base = word(out, 0).to::<usize>();
    assert_eq!(word(out, base), u(mc.alpha), "alpha");
    assert_eq!(word(out, base + 32), u(mc.beta), "beta");
    assert_eq!(array(out, base, base + 96), mc.x_inner_rest.iter().map(|&v| u(v)).collect::<Vec<_>>(), "x");
    assert_eq!(array(out, base, base + 128), mc.r_inner_rest.iter().map(|&v| u(v)).collect::<Vec<_>>(), "r");
    assert_eq!(array(out, base, base + 160), mc.z_partial.iter().map(|&v| u(v)).collect::<Vec<_>>(), "z_partial");
    assert_eq!(word(out, base + 192), u(mc.running), "running");
}

#[test]
fn contract_matches_the_mirror_on_an_eight_response_chunk() {
    let n = 8;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter evm contract entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let lifted = prove(&LiftKey::new(program.clone()), &statement, &proof, MAX_CHUNK).expect("lift");
    let dom = domain(&statement.digest(n, MAX_CHUNK as u32), 0);
    let data = encode_chunk(&lifted.chunks[0], n);
    let mc = verify_chunk(&program, &lifted.words, &dom, &data).expect("mirror verifies");
    let mut words = Writer::default();
    lifted.words.iter().flatten().for_each(|&w| words.f128_native(w));
    let mut evm = Evm::new();
    let (verifier, deploy_gas) = evm.deploy(artifact("FlockVerifier.sol", "FlockVerifier"));
    let call = |data: &[u8]| {
        encode("verifyChunk(bytes,bytes,uint256,bytes)", |a| {
            a.bytes(&dom).bytes(&words.bytes).uint(U256::from(n)).bytes(data)
        })
    };
    let out = evm.call(verifier, call(&data));
    assert!(out.success, "contract refused: {}", String::from_utf8_lossy(&out.output));
    assert_claim(&out.output, &mc);
    let mut last = 0u64;
    for (topics, body) in &out.logs {
        let id = U256::from_be_bytes(topics[1]).to::<u64>();
        let left = U256::from_be_slice(&body[..32]).to::<u64>();
        if id > 0 {
            eprintln!("phase {id}: {} gas", last - left);
        }
        last = left;
    }
    eprintln!(
        "deploy {deploy_gas} gas; chunk of {n}: {} gas in all, {} of it execution, calldata {} bytes",
        out.gas,
        out.execution(),
        data.len()
    );
    for at in [10, data.len() / 3, data.len() / 2, data.len() - 20] {
        let mut bad = data.clone();
        bad[at] ^= 0x10;
        let out = evm.call(verifier, call(&bad));
        let refused_by_mirror = verify_chunk(&program, &lifted.words, &dom, &bad).is_err();
        assert!(!out.success || !refused_by_mirror, "byte {at}: the contract accepted what the mirror refused");
    }
}

fn deploy_lift(evm: &mut Evm, statement: &Statement, min: usize) -> revm::primitives::Address {
    let mut code = artifact("FlockLift.sol", "FlockLift");
    let fingerprint = zkboo_circuit_hash::hash_circuit::<_, pofseed_flock_lift_statement::H>(&statement.circuit());
    code.extend_from_slice(&fingerprint);
    code.extend_from_slice(&statement.chain_code);
    code.extend_from_slice(&U256::from(statement.index).to_be_bytes::<32>());
    code.extend_from_slice(&U256::from(min).to_be_bytes::<32>());
    code.extend_from_slice(&counts(statement).to_be_bytes::<32>());
    let slim = pofseed_flock_lift::chunk_rm::profile() == flock_prover::pcs::ligerito::LigeritoProfile::Slim;
    code.extend_from_slice(&U256::from(slim as u8).to_be_bytes::<32>());
    return evm.deploy(code).0;
}

fn counts(statement: &Statement) -> U256 {
    let y = &statement.expected_output;
    return U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
}

#[test]
fn lift_contract_verifies_a_lift_and_its_gate_refuses_forgeries() {
    let n = 8;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter evm lift entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let lifted = prove(&LiftKey::new(program.clone()), &statement, &proof, 4).expect("lift");
    let mut evm = Evm::new();
    let lift = deploy_lift(&mut evm, &statement, n);
    let call_with = |binding: &[u8], data: &[u8], counts: U256| {
        encode("verify(bytes,uint256,bytes,bytes)", |a| {
            a.bytes(&statement.expected_output.as_bytes()).uint(counts).bytes(binding).bytes(data)
        })
    };
    let call = |binding: &[u8], data: &[u8]| call_with(binding, data, counts(&statement));
    let data = pofseed_flock_lift_evm::calldata::encode_lift(&lifted);
    let out = evm.call(lift, call(BINDING, &data));
    assert!(out.success, "lift refused: {}", hex::encode(&out.output));
    let words: Vec<U256> = (0..word(&out.output, 32).to::<usize>()).map(|i| word(&out.output, 64 + 32 * i)).collect();
    assert_eq!(words.len(), 112 * 2);
    for c in 0..2 {
        let dom = domain(&statement.digest(n, 4), c);
        let chunk = encode_chunk(&lifted.chunks[c], 4);
        let mc = verify_chunk(&program, &lifted.words[4 * c..4 * c + 4], &dom, &chunk).expect("mirror verifies");
        let b = 112 * c;
        assert_eq!(words[b], u(mc.alpha));
        assert_eq!(words[b + 3], u(mc.running));
        assert_eq!(words[b + 48..b + 112].to_vec(), mc.z_partial.iter().map(|&v| u(v)).collect::<Vec<_>>());
    }
    eprintln!("lift of {n} in 2 chunks: {} gas, calldata {} bytes", out.gas, data.len());
    assert!(!evm.call(lift, call(b"another binding", &data)).success, "a different binding was accepted");
    let mut forged = lifted.clone();
    forged.words[1][0] = if forged.words[1][0].lo == 1 { F128::new(2, 0) } else { F128::new(1, 0) };
    let bad = pofseed_flock_lift_evm::calldata::encode_lift(&forged);
    assert!(!evm.call(lift, call(BINDING, &bad)).success, "a changed challenge was accepted");
    let y = &statement.expected_output;
    let other_split = U256::from((y.as_vec::<u8>().len() - 8) | ((y.as_vec::<u64>().len() + 1) << 32));
    assert!(!evm.call(lift, call_with(BINDING, &data, other_split)).success, "another split of the same payload was accepted");
}

#[test]
fn fiat_shamir_gate_refuses_what_the_native_gate_refuses() {
    let n = 12;
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter evm gate entropy", BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET)));
    let circuit = statement.circuit();
    let words: Vec<Vec<F128>> = proof
        .iter()
        .map(|r| pofseed_flock_lift_block::native::io_words(&program, &circuit, &statement.expected_output, r).expect("replay"))
        .collect();
    let unopened: Vec<[u8; 32]> = proof.iter().map(|r| *r.commitment_digest_unopened()).collect();
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("GateProbe.sol", "GateProbe"));
    let mut run = |binding: &[u8], words: &[Vec<F128>], unopened: &[[u8; 32]], output: &[u8]| {
        let mut w = Writer::default();
        words.iter().flatten().for_each(|&v| w.f128_native(v));
        unopened.iter().for_each(|d| w.hash(d));
        let out = evm.call(
            probe,
            encode("gate(bytes,uint256,bytes,uint256,bytes)", |a| {
                a.bytes(output).uint(counts(&statement)).bytes(binding).uint(U256::from(n)).bytes(&w.bytes)
            }),
        );
        (out.success, out.gas)
    };
    let y = statement.expected_output.as_bytes();
    let (ok, gas) = run(BINDING, &words, &unopened, &y);
    assert!(ok, "the genuine gate inputs were refused");
    eprintln!("gate over {n} responses: {gas} gas");
    assert!(!run(b"other", &words, &unopened, &y).0, "another binding passed the gate");
    let mut bad = unopened.clone();
    bad[5][0] ^= 1;
    assert!(!run(BINDING, &words, &bad, &y).0, "a changed unopened digest passed the gate");
    for i in [0, 7] {
        let mut w = words.clone();
        let next = match w[i][0].lo {
            1 => 2,
            2 => 4,
            _ => 1,
        };
        w[i][0] = F128::new(next, 0);
        assert!(!run(BINDING, &w, &unopened, &y).0, "a changed challenge at {i} passed the gate");
        for bad_word in [F128::ZERO, F128::new(3, 0), F128::new(8, 0), F128::new(1, 1)] {
            let mut w = words.clone();
            w[i][0] = bad_word;
            assert!(!run(BINDING, &w, &unopened, &y).0, "a challenge word {bad_word:?} at {i} passed the gate");
        }
        let mut w = words.clone();
        w[i][6].lo ^= 1 << 9;
        assert!(!run(BINDING, &w, &unopened, &y).0, "a changed output share at {i} passed the gate");
        let mut w = words.clone();
        w[i][2].hi ^= 1;
        assert!(!run(BINDING, &w, &unopened, &y).0, "a changed view digest at {i} passed the gate");
    }
    let mut y2 = y.clone();
    let last = y2.len() - 33;
    y2[last] ^= 1;
    assert!(!run(BINDING, &words, &unopened, &y2).0, "a changed expected output passed the gate");
}
