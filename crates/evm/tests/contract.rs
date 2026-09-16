// SPDX-License-Identifier: LGPL-3.0-or-later

//! The contract verifies a genuine chunk exactly as the mirror does, and refuses tampering.

use std::sync::Arc;

use flock_prover::field::F128;
use pofseed_flock_lift::lift::{MAX_CHUNK, Statement, domain, prove};
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
    let lifted = prove(&program, &statement, &proof, MAX_CHUNK).expect("lift");
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
