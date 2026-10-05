// SPDX-License-Identifier: LGPL-3.0-or-later

//! The on-chain verifier of a wrapped lift: its constants, the calldata encoding of a lift, and a
//! verifier that reads the encoding with one forward cursor and computes what the contract does.

pub mod encode;
pub mod opening;
pub mod outer;
pub mod sol;
pub mod staged;
pub mod structure;
pub mod trace;
pub mod vk;
pub mod whir;

use flock_prover::challenger::Challenger;
use pofseed_flock_lift::wrapped::WrappedLift;

use crate::mirror::{Reader, Reject, Result};

/// Encodes a wrapped lift's proofs: the outer proof with the
/// two evaluations of the wiring's tables its verifier is given, the
/// outer commitment's opening, and the structure proof.
pub fn encode_proofs(vk: &vk::Vk, lifted: &WrappedLift, live: flock_prover::field::F128, masked: flock_prover::field::F128) -> Vec<u8> {
    let (mut data, opening) = encode::encode_outer(vk, &lifted.wrap, live, masked);
    let opening: pofseed_flock_lift_whir::whir::Proof = bincode::deserialize(&opening).expect("a WHIR opening");
    data.extend(whir::encode(&vk.whir, &opening));
    data.extend(structure::encode(&vk.structure, &lifted.structure));
    return data;
}

/// Encodes a wrapped lift: every response's published words and unopened digest, then its proofs.
pub fn encode_lift(vk: &vk::Vk, lifted: &WrappedLift, words: &[Vec<flock_prover::field::F128>], live: flock_prover::field::F128, masked: flock_prover::field::F128) -> Vec<u8> {
    let mut w = crate::calldata::Writer::default();
    assert_eq!(words.len(), vk.responses);
    for row in words {
        assert_eq!(row.len(), vk.n_io);
        row.iter().for_each(|&v| w.f128_native(v));
    }
    lifted.unopened.iter().for_each(|d| w.hash(d));
    w.raw(&encode_proofs(vk, lifted, live, masked));
    return w.bytes;
}

/// The published words and the unopened digest of every response, read from a lift's encoding.
pub fn read_responses(vk: &vk::Vk, rd: &mut Reader) -> Result<(Vec<Vec<flock_prover::field::F128>>, Vec<[u8; 32]>)> {
    let words = (0..vk.responses).map(|_| (0..vk.n_io).map(|_| rd.f128_native()).collect()).collect::<Result<_>>()?;
    let unopened = (0..vk.responses).map(|_| rd.hash()).collect::<Result<_>>()?;
    return Ok((words, unopened));
}

/// Verifies the proofs of a wrapped lift over the responses' published `words`, reading their
/// encoding from `rd`: returns the transcript's last chaining value.
pub fn verify_proofs(vk: &vk::Vk, rd: &mut Reader, words: &[Vec<flock_prover::field::F128>]) -> Result<[u8; 32]> {
    let public = outer::read_public(vk, rd, words)?;
    let (p, mut tr, cap) = outer::piops(vk, rd, &public)?;
    trace::mark(5, &tr);
    let (opened, child) = opening::transport(vk, rd, &mut tr, &p)?;
    trace::mark(8, &child);
    whir::verify(&vk.whir, &cap, &[opened.point.clone()], &[opened.value], rd, &mut tr)?;
    trace::mark(9, &tr);
    tr.merge_child(child);
    if opened.target != opened.value * opened.weight {
        return Err(Reject("transport"));
    }
    trace::mark(10, &tr);
    structure::verify(&vk.structure, &p.claims, rd, &mut tr)?;
    trace::mark(20, &tr);
    if rd.remaining() != 0 {
        return Err(Reject("trailing bytes"));
    }
    return Ok(tr.digest());
}

/// Verifies a wrapped lift of `statement` from its encoding: the proofs, then the global
/// Fiat-Shamir gate over the published words and the unopened digests.
pub fn verify_lift(vk: &vk::Vk, program: &pofseed_flock_lift_block::program::Program, statement: &pofseed_flock_lift::lift::Statement, data: &[u8]) -> Result<[u8; 32]> {
    let mut rd = Reader::new(data);
    let (words, unopened) = read_responses(vk, &mut rd)?;
    let digest = verify_proofs(vk, &mut rd, &words)?;
    pofseed_flock_lift::lift::gate(program, statement, &words, &unopened).map_err(|_| Reject("Fiat-Shamir gate"))?;
    return Ok(digest);
}
