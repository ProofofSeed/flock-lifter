// SPDX-License-Identifier: LGPL-3.0-or-later

//! The on-chain discharge of a lift's matrix claims through its committed entry list: the
//! Keccak-f sub-blocks' structured part, then the matrix proof, each in its own call.

use pofseed_flock_lift::matrix::MatrixCommitment;
use pofseed_flock_lift_block::program::Program;
use revm::primitives::{Address, U256, keccak256};

use crate::evm::{Evm, Outcome, artifact, encode};

/// Deploys the contract of `program`'s structured part: the discharge contract without a row
/// stream.
pub fn deploy_structured(evm: &mut Evm, program: &Program) -> Address {
    let g = program.geometry();
    let mut code = artifact("Discharge.sol", "FlockDischarge");
    for v in [g.k_log(), g.head_subs(), g.subs_per_slot(), g.prg_blocks(), g.in_blocks(), 0] {
        code.extend_from_slice(&U256::from(v).to_be_bytes::<32>());
    }
    code.extend_from_slice(&[0u8; 32]);
    return evm.deploy(code).0;
}

/// Deploys the matrix verifier pinned to the entry commitment `key`.
pub fn deploy_matrix(evm: &mut Evm, key: &MatrixCommitment, slim: bool) -> (Address, u64) {
    let mut code = artifact("FlockMatrix.sol", "FlockMatrix");
    code.extend_from_slice(&keccak256(key.commitment.cap.concat()).0);
    code.extend_from_slice(&U256::from(slim as u8).to_be_bytes::<32>());
    return evm.deploy(code);
}

fn words(out: &[u8]) -> Vec<U256> {
    let n = U256::from_be_slice(&out[32..64]).to::<usize>();
    return (0..n).map(|i| U256::from_be_slice(&out[64 + 32 * i..96 + 32 * i])).collect();
}

/// The structured part of every packed claim, and the call that computed it.
pub fn structured(evm: &mut Evm, at: Address, claims: &[U256]) -> (Outcome, Vec<U256>) {
    let out = evm.call(at, encode("keccakPart(uint256[])", |a| a.uints(claims)));
    assert!(out.success, "keccakPart failed: {}", String::from_utf8_lossy(&out.output));
    let parts = words(&out.output);
    return (out, parts);
}

/// Calls the matrix verifier at `at` on the packed claims, their structured parts, the lift's
/// statement digest and the encoded matrix proof.
pub fn verify(evm: &mut Evm, at: Address, claims: &[U256], parts: &[U256], digest: &[u8; 32], proof: &[u8]) -> Outcome {
    return evm.call(
        at,
        encode("verify(uint256[],uint256[],bytes32,bytes)", |a| {
            a.uints(claims).uints(parts).uint(U256::from_be_bytes(*digest)).bytes(proof)
        }),
    );
}
