// SPDX-License-Identifier: LGPL-3.0-or-later

//! The on-chain discharge of a lift's matrix claims through its committed entry list, in one call
//! that also computes the claims' structured parts.

use pofseed_flock_lift::matrix::MatrixCommitment;
use pofseed_flock_lift_block::program::Program;
use revm::primitives::{Address, U256, keccak256};

use crate::evm::{Evm, Outcome, artifact, encode};

/// Deploys the matrix verifier of `program`, pinned to its entry commitment `key`.
pub fn deploy_matrix(evm: &mut Evm, program: &Program, key: &MatrixCommitment, slim: bool) -> (Address, u64) {
    let g = program.geometry();
    let mut code = artifact("FlockMatrix.sol", "FlockMatrix");
    code.extend_from_slice(&keccak256(key.commitment.cap.concat()).0);
    for v in [slim as usize, g.head_subs(), g.keccak_subs()] {
        code.extend_from_slice(&U256::from(v).to_be_bytes::<32>());
    }
    return evm.deploy(code);
}

/// Calls the matrix verifier at `at` on the packed claims, the lift's statement digest and the
/// encoded matrix proof.
pub fn verify(evm: &mut Evm, at: Address, claims: &[U256], digest: &[u8; 32], proof: &[u8]) -> Outcome {
    return evm.call(
        at,
        encode("verify(uint256[],bytes32,bytes)", |a| a.uints(claims).uint(U256::from_be_bytes(*digest)).bytes(proof)),
    );
}
