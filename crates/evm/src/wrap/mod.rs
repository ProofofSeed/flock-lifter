// SPDX-License-Identifier: LGPL-3.0-or-later

//! The on-chain verifier of a wrapped lift: its constants, the calldata encoding of a lift, and a
//! verifier that reads the encoding with one forward cursor and computes what the contract does.

pub mod encode;
pub mod opening;
pub mod outer;
pub mod structure;
pub mod vk;
pub mod whir;

use flock_prover::challenger::Challenger;
use pofseed_flock_lift::wrapped::WrappedLift;

use crate::mirror::{Reader, Reject, Result};

/// Encodes a wrapped lift's proofs: the outer proof with the two evaluations of the wiring's
/// tables its verifier is given, the outer commitment's opening, and the structure proof.
pub fn encode_proofs(vk: &vk::Vk, lifted: &WrappedLift, live: flock_prover::field::F128, masked: flock_prover::field::F128) -> Vec<u8> {
    let (mut data, opening) = encode::encode_outer(vk, &lifted.wrap, live, masked);
    let opening: pofseed_flock_lift_whir::whir::Proof = bincode::deserialize(&opening).expect("a WHIR opening");
    data.extend(whir::encode(&vk.whir, &opening));
    data.extend(structure::encode(&vk.structure, &lifted.structure));
    return data;
}

/// Verifies the proofs of a wrapped lift from their encoding: returns the public segment and the
/// transcript's last chaining value.
pub fn verify_proofs(vk: &vk::Vk, data: &[u8]) -> Result<(Vec<flock_prover::field::F128>, [u8; 32])> {
    let mut rd = Reader::new(data);
    let public = outer::read_public(vk, &mut rd)?;
    let (p, mut tr, cap) = outer::piops(vk, &mut rd, &public)?;
    let (opened, child) = opening::transport(vk, &mut rd, &mut tr, &p)?;
    whir::verify(&vk.whir, &cap, &[opened.point.clone()], &[opened.value], &mut rd, &mut tr)?;
    tr.merge_child(child);
    if opened.target != opened.value * opened.weight {
        return Err(Reject("transport"));
    }
    structure::verify(&vk.structure, &p.claims, &mut rd, &mut tr)?;
    if rd.remaining() != 0 {
        return Err(Reject("trailing bytes"));
    }
    return Ok((public, tr.digest()));
}
