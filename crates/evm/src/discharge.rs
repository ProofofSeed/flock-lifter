// SPDX-License-Identifier: LGPL-3.0-or-later

//! The matrix discharge as the contract runs it: the explicit-row stream of a block, its hash
//! chain, the packing of matrix claims, and a driver that runs the discharge in the EVM phase
//! by phase.

use flock_prover::field::F128;
use pofseed_flock_lift_block::program::Program;
use revm::primitives::{Address, U256, keccak256};

use crate::{
    evm::{Evm, artifact, encode},
    mirror::MatrixClaim,
};

/// Encodes explicit rows `from..to` of `program`.
pub fn encode_rows(program: &Program, from: usize, to: usize) -> Vec<u8> {
    let mut out = Vec::new();
    for r in from..to {
        let (col, a, b) = program.explicit_row(r);
        out.extend_from_slice(&col.to_be_bytes());
        out.extend_from_slice(&(a.len() as u16).to_be_bytes());
        out.extend_from_slice(&(b.len() as u16).to_be_bytes());
        for &c in a.iter().chain(b) {
            out.extend_from_slice(&c.to_be_bytes());
        }
    }
    return out;
}

/// The row ranges of a stream cut into segments of `rows_per_segment` rows.
pub fn segments(program: &Program, rows_per_segment: usize) -> Vec<(usize, usize)> {
    let n = program.explicit_rows();
    return (0..n.div_ceil(rows_per_segment))
        .map(|i| (i * rows_per_segment, ((i + 1) * rows_per_segment).min(n)))
        .collect();
}

/// The hash chain over a stream's segments.
pub fn rows_digest(program: &Program, segs: &[(usize, usize)]) -> [u8; 32] {
    let mut chain = [0u8; 32];
    for &(from, to) in segs {
        let hashed = keccak256(encode_rows(program, from, to));
        let mut buf = chain.to_vec();
        buf.extend_from_slice(hashed.as_slice());
        chain = keccak256(&buf).0;
    }
    return chain;
}

fn u(v: F128) -> U256 {
    return U256::from(((v.hi as u128) << 64) | v.lo as u128);
}

/// A claim packed as the discharge contract reads it.
pub fn pack_claim(claim: &MatrixClaim, z: F128) -> Vec<U256> {
    let mut out = vec![u(claim.alpha), u(claim.beta), u(z), u(claim.running)];
    out.extend(claim.x_inner_rest.iter().map(|&v| u(v)));
    out.extend(claim.r_inner_rest.iter().map(|&v| u(v)));
    out.extend(claim.z_partial.iter().map(|&v| u(v)));
    return out;
}

/// Gas of each phase of one discharge.
#[derive(Clone, Debug, Default)]
pub struct DischargeGas {
    /// The Keccak-f sub-blocks' part: execution gas.
    pub keccak: u64,
    /// The explicit rows: execution gas per segment.
    pub rows: Vec<u64>,
    /// The explicit rows: calldata gas per segment.
    pub rows_calldata: Vec<u64>,
    /// The final check: execution gas.
    pub finish: u64,
    /// Whether the discharge accepted.
    pub accepted: bool,
}

fn words(out: &[u8]) -> Vec<U256> {
    let n = U256::from_be_slice(&out[32..64]).to::<usize>();
    return (0..n).map(|i| U256::from_be_slice(&out[64 + 32 * i..96 + 32 * i])).collect();
}

/// Deploys a discharge contract for `program` and the given stream.
pub fn deploy(evm: &mut Evm, program: &Program, segs: &[(usize, usize)]) -> Address {
    let g = program.geometry();
    let mut code = artifact("Discharge.sol", "FlockDischarge");
    for v in [g.k_log(), g.head_subs(), g.keccak_subs()] {
        code.extend_from_slice(&U256::from(v).to_be_bytes::<32>());
    }
    code.extend_from_slice(&rows_digest(program, segs));
    return evm.deploy(code).0;
}

/// Runs the discharge of `claims` (already packed) through the contract at `at`.
pub fn run(evm: &mut Evm, at: Address, program: &Program, segs: &[(usize, usize)], claims: &[U256]) -> DischargeGas {
    let mut gas = DischargeGas::default();
    let out = evm.call(at, encode("keccakPart(uint256[])", |a| a.uints(claims)));
    assert!(out.success, "keccakPart failed: {}", String::from_utf8_lossy(&out.output));
    gas.keccak = out.execution();
    let part = words(&out.output);
    let mut acc = vec![U256::ZERO; 128 * part.len() / 64];
    let mut chain = [0u8; 32];
    for &(from, to) in segs {
        let seg = encode_rows(program, from, to);
        let data = encode("rows(uint256[],uint256[],bytes32,bytes)", |a| {
            a.uints(claims).uints(&acc).uint(U256::from_be_bytes(chain)).bytes(&seg)
        });
        let out = evm.call(at, data);
        assert!(out.success, "rows failed: {}", String::from_utf8_lossy(&out.output));
        gas.rows.push(out.execution());
        gas.rows_calldata.push(out.intrinsic);
        let offset = U256::from_be_slice(&out.output[..32]).to::<usize>();
        let n = U256::from_be_slice(&out.output[offset..offset + 32]).to::<usize>();
        acc = (0..n)
            .map(|i| U256::from_be_slice(&out.output[offset + 32 + 32 * i..offset + 64 + 32 * i]))
            .collect();
        chain = out.output[32..64].try_into().expect("chain");
    }
    let out = evm.call(
        at,
        encode("finish(uint256[],uint256[],uint256[],bytes32)", |a| {
            a.uints(claims).uints(&part).uints(&acc).uint(U256::from_be_bytes(chain))
        }),
    );
    gas.finish = out.execution();
    gas.accepted = out.success;
    return gas;
}
