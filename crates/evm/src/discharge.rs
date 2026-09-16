// SPDX-License-Identifier: LGPL-3.0-or-later

//! The matrix discharge as the contract runs it: the stream of a block cut into segments, its
//! hash chain, the packing of matrix claims, and a driver that runs the discharge in the EVM
//! phase by phase.

use flock_prover::field::F128;
use pofseed_flock_lift_block::{form::CONST, program::Program};
use revm::primitives::{Address, U256, keccak256};

use crate::{
    evm::{Evm, artifact, encode},
    mirror::MatrixClaim,
    stream::{records, segments as cut},
};

/// A block's stream, cut into segments of at most `segment_bytes` bytes.
pub struct Stream {
    /// The segments, in order.
    pub segments: Vec<Vec<u8>>,
    /// Head words any explicit row refers to.
    pub head_words: usize,
}

impl Stream {
    /// The stream of `program`.
    pub fn new(program: &Program, segment_bytes: usize) -> Self {
        let recs = records(program);
        let head = (program.geometry().head_subs() as u32) << 16;
        let mut head_words = 0u32;
        for r in 0..program.explicit_rows() {
            let (col, a, b) = program.explicit_row(r);
            for &c in std::iter::once(&col).chain(a).chain(b) {
                if c < head && c != CONST {
                    head_words = head_words.max((c >> 6) + 1);
                }
            }
        }
        return Self {
            segments: cut(&recs, segment_bytes),
            head_words: head_words as usize,
        };
    }

    /// The hash chain over the segments.
    pub fn digest(&self) -> [u8; 32] {
        let mut chain = [0u8; 32];
        for seg in &self.segments {
            let mut hashed = [0u8; 32];
            for piece in seg.chunks(32768) {
                let mut buf = hashed.to_vec();
                buf.extend_from_slice(piece);
                hashed = keccak256(&buf).0;
            }
            let mut buf = chain.to_vec();
            buf.extend_from_slice(&hashed);
            chain = keccak256(&buf).0;
        }
        return chain;
    }

    /// Bytes in all.
    pub fn len(&self) -> usize {
        return self.segments.iter().map(Vec::len).sum();
    }

    /// Whether the stream is empty.
    pub fn is_empty(&self) -> bool {
        return self.len() == 0;
    }
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
    /// The stream: execution gas per segment.
    pub rows: Vec<u64>,
    /// The stream: the part of each segment's execution spent building its tables.
    pub setup: Vec<u64>,
    /// The stream: intrinsic gas per segment.
    pub rows_calldata: Vec<u64>,
    /// The final check: execution gas.
    pub finish: u64,
    /// Intrinsic gas of the Keccak-part and final-check calls.
    pub intrinsic: u64,
    /// Whether the discharge accepted.
    pub accepted: bool,
}

fn words(out: &[u8]) -> Vec<U256> {
    let n = U256::from_be_slice(&out[32..64]).to::<usize>();
    return (0..n).map(|i| U256::from_be_slice(&out[64 + 32 * i..96 + 32 * i])).collect();
}

/// Deploys a discharge contract for `program` and its stream.
pub fn deploy(evm: &mut Evm, program: &Program, stream: &Stream) -> Address {
    let g = program.geometry();
    let mut code = artifact("Discharge.sol", "FlockDischarge");
    for v in [g.k_log(), g.head_subs(), g.subs_per_slot(), g.prg_blocks(), g.in_blocks(), stream.head_words] {
        code.extend_from_slice(&U256::from(v).to_be_bytes::<32>());
    }
    code.extend_from_slice(&stream.digest());
    return evm.deploy(code).0;
}

/// Runs the discharge of `claims` (already packed) through the contract at `at`.
pub fn run(evm: &mut Evm, at: Address, stream: &Stream, claims: &[U256]) -> DischargeGas {
    let mut gas = DischargeGas::default();
    let out = evm.call(at, encode("keccakPart(uint256[])", |a| a.uints(claims)));
    assert!(out.success, "keccakPart failed: {}", String::from_utf8_lossy(&out.output));
    gas.keccak = out.execution();
    gas.intrinsic += out.intrinsic;
    let part = words(&out.output);
    let mut state = vec![U256::ZERO; 2 * part.len() / 64];
    let mut chain = [0u8; 32];
    for seg in &stream.segments {
        let data = encode("rows(uint256[],uint256[],bytes32,bytes)", |a| {
            a.uints(claims).uints(&state).uint(U256::from_be_bytes(chain)).bytes(seg)
        });
        let out = evm.call(at, data);
        assert!(out.success, "rows failed: {}", String::from_utf8_lossy(&out.output));
        gas.rows.push(out.execution());
        gas.rows_calldata.push(out.intrinsic);
        let marks: Vec<u64> = out.logs.iter().map(|(_, body)| U256::from_be_slice(&body[..32]).to::<u64>()).collect();
        if marks.len() == 2 {
            gas.setup.push(out.execution() - (marks[0] - marks[1]));
        }
        let offset = U256::from_be_slice(&out.output[..32]).to::<usize>();
        let n = U256::from_be_slice(&out.output[offset..offset + 32]).to::<usize>();
        state = (0..n)
            .map(|i| U256::from_be_slice(&out.output[offset + 32 + 32 * i..offset + 64 + 32 * i]))
            .collect();
        chain = out.output[32..64].try_into().expect("chain");
    }
    let out = evm.call(
        at,
        encode("finish(uint256[],uint256[],uint256[],bytes32)", |a| {
            a.uints(claims).uints(&part).uints(&state).uint(U256::from_be_bytes(chain))
        }),
    );
    gas.finish = out.execution();
    gas.intrinsic += out.intrinsic;
    gas.accepted = out.success;
    return gas;
}
