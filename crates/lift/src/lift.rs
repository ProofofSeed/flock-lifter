// SPDX-License-Identifier: LGPL-3.0-or-later

//! The lift of a whole ZKBoo proof: Flock proofs over chunks of its responses, the words they
//! publish, the unopened digests, and the verifier that checks every chunk and runs the global
//! Fiat-Shamir gate natively.

use std::sync::Arc;

use flock_prover::field::F128;
use pofseed_flock_lift_block::{
    native,
    program::{Program, WitnessError},
};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit, LIFT_JOURNAL_VERSION, LiftJournal, S};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use zkboo::{
    crypto::{GeneratesRandom, HashPRG, Hasher, PseudoRandomGenerator, TAG_CHALLENGE, absorb_framed},
    prover::{
        challenge::{ChallengeGenerator, Party},
        proof::Response,
    },
    word::{Word, Words},
};
use zkboo_circuit_hash::hash_circuit;

use crate::chunk_rm::{ChunkProofRm, ChunkRmError, prove_chunk, verify_chunk};

/// Largest number of responses one chunk proves: 128 blocks of `2^28` bits commit at `m = 35`,
/// the largest size Ligerito has a configuration for.
pub const MAX_CHUNK: usize = 128;

/// Version of the lift, bound into every chunk's transcript domain.
pub const LIFT_VERSION: &[u8] = b"pofseed-flock-lift-v1";

/// A lifted ZKBoo proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiftedProof {
    /// Responses per chunk; the last chunk may hold fewer.
    pub chunk: u32,
    /// One Flock proof per chunk.
    pub chunks: Vec<ChunkProofRm>,
    /// The published words of every response, in response order.
    pub words: Vec<Vec<F128>>,
    /// The unopened view digest of every response.
    pub unopened: Vec<[u8; 32]>,
}

/// The public statement a lift is proved and verified against.
#[derive(Clone, Debug)]
pub struct Statement {
    /// Parent chain code.
    pub chain_code: Vec<u8>,
    /// Child index.
    pub index: u32,
    /// The circuit output being proven.
    pub expected_output: Words,
    /// The challenge binding.
    pub binding: Vec<u8>,
}

/// Why a lift could not be produced or was refused.
#[derive(Debug)]
pub enum LiftError {
    /// ZKBoo's replay refused a response.
    Replay(usize),
    /// A response does not have the statement's shape.
    Witness(usize, WitnessError),
    /// The lifted proof's parts disagree in length, or its chunk size is invalid.
    Shape,
    /// A chunk proof was refused.
    Chunk(usize, ChunkRmError),
    /// A published challenge word is not one-hot.
    Challenge(usize),
    /// The challenges are not the ones the Fiat-Shamir transcript derives.
    FiatShamir,
}

impl Statement {
    /// The public-only circuit of the statement.
    pub fn circuit(&self) -> HardenedChildCircuit {
        return HardenedChildCircuit::public_only(self.chain_code.clone(), self.index);
    }

    /// Digest of the statement together with the lift's response count and chunk size.
    pub fn digest(&self, num_responses: usize, chunk: u32) -> [u8; 32] {
        let mut h = H::new();
        absorb_framed(&mut h, LIFT_VERSION, &hash_circuit::<_, H>(&self.circuit()));
        absorb_framed(&mut h, b"chain-code", &self.chain_code);
        absorb_framed(&mut h, b"index", &self.index.to_le_bytes());
        absorb_framed(&mut h, b"expected-output", &self.expected_output.as_bytes());
        absorb_framed(&mut h, b"binding", &self.binding);
        absorb_framed(&mut h, b"responses", &(num_responses as u64).to_le_bytes());
        absorb_framed(&mut h, b"chunk", &chunk.to_le_bytes());
        return h.finalize();
    }
}

fn domain(digest: &[u8; 32], chunk_index: usize) -> Vec<u8> {
    let mut d = LIFT_VERSION.to_vec();
    d.extend_from_slice(digest);
    d.extend_from_slice(&(chunk_index as u64).to_le_bytes());
    return d;
}

/// Lifts a ZKBoo proof of `statement`, proving at most `chunk` responses per Flock proof.
pub fn prove(
    program: &Arc<Program>,
    statement: &Statement,
    proof: &[Response<S, S>],
    chunk: usize,
) -> Result<LiftedProof, LiftError> {
    assert!((1..=MAX_CHUNK).contains(&chunk), "chunk size must be in 1..={MAX_CHUNK}");
    let circuit = statement.circuit();
    for (i, response) in proof.iter().enumerate() {
        program.check_response(response).map_err(|e| LiftError::Witness(i, e))?;
    }
    let words: Vec<Vec<F128>> = proof
        .par_iter()
        .enumerate()
        .map(|(i, r)| native::io_words(program, &circuit, &statement.expected_output, r).map_err(|_| LiftError::Replay(i)))
        .collect::<Result<_, _>>()?;
    let unopened = proof.iter().map(|r| *r.commitment_digest_unopened()).collect();
    let digest = statement.digest(proof.len(), chunk as u32);
    let mut chunks = Vec::new();
    for (i, (responses, publics)) in proof.chunks(chunk).zip(words.chunks(chunk)).enumerate() {
        let c = prove_chunk(program, responses, publics, &domain(&digest, i))
            .map_err(|e| LiftError::Witness(i * chunk, e))?;
        chunks.push(c);
    }
    return Ok(LiftedProof {
        chunk: chunk as u32,
        chunks,
        words,
        unopened,
    });
}

fn words_from_bits(shape_of: &Words, bits: &[bool]) -> Words {
    fn take<W: Word>(n: usize, bits: &[bool], pos: &mut usize) -> Vec<W> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            let mut w = W::ZERO;
            for b in 0..W::WIDTH {
                if bits[*pos + b] {
                    w = w ^ (W::ONE << b);
                }
            }
            *pos += W::WIDTH;
            out.push(w);
        }
        return out;
    }
    let mut words = Words::new();
    let mut pos = 0;
    *words.as_vec_mut::<u8>() = take::<u8>(shape_of.as_vec::<u8>().len(), bits, &mut pos);
    *words.as_vec_mut::<u32>() = take::<u32>(shape_of.as_vec::<u32>().len(), bits, &mut pos);
    *words.as_vec_mut::<u64>() = take::<u64>(shape_of.as_vec::<u64>().len(), bits, &mut pos);
    return words;
}

fn f128_bits(words: &[F128]) -> Vec<bool> {
    return words
        .iter()
        .flat_map(|w| [w.lo, w.hi])
        .flat_map(|l| (0..64).map(move |b| (l >> b) & 1 == 1))
        .collect();
}

/// Verifies a lifted proof of `statement`, returning the journal it attests.
pub fn verify(program: &Arc<Program>, statement: &Statement, lifted: &LiftedProof) -> Result<LiftJournal, LiftError> {
    let n = lifted.words.len();
    let chunk = lifted.chunk as usize;
    if lifted.unopened.len() != n || chunk == 0 || chunk > MAX_CHUNK || lifted.chunks.len() != n.div_ceil(chunk) {
        return Err(LiftError::Shape);
    }
    let digest = statement.digest(n, lifted.chunk);
    for (i, (c, publics)) in lifted.chunks.iter().zip(lifted.words.chunks(chunk)).enumerate() {
        verify_chunk(program, publics, c, &domain(&digest, i)).map_err(|e| LiftError::Chunk(i, e))?;
    }
    let ow = program.geometry().out_words();
    let y = &statement.expected_output;
    let mut hasher = H::new();
    absorb_framed(&mut hasher, TAG_CHALLENGE, &statement.binding);
    let mut challenges = Vec::with_capacity(n);
    for (i, w) in lifted.words.iter().enumerate() {
        let c = match (w[0].lo, w[0].hi) {
            (1, 0) => 0,
            (2, 0) => 1,
            (4, 0) => 2,
            _ => return Err(LiftError::Challenge(i)),
        };
        challenges.push(c);
        let digests: [S; 2] = [0, 1].map(|s| {
            let mut d = [0u8; 32];
            d[..8].copy_from_slice(&w[1 + 2 * s].lo.to_le_bytes());
            d[8..16].copy_from_slice(&w[1 + 2 * s].hi.to_le_bytes());
            d[16..24].copy_from_slice(&w[2 + 2 * s].lo.to_le_bytes());
            d[24..32].copy_from_slice(&w[2 + 2 * s].hi.to_le_bytes());
            d
        });
        let shares = [0, 1].map(|s| words_from_bits(y, &f128_bits(&w[5 + s * ow..5 + (s + 1) * ow])));
        let third = (&(y ^ &shares[0]).expect("shares have the output's shape") ^ &shares[1])
            .expect("shares have the output's shape");
        for p in 0..3 {
            let (d, o) = match (p + 3 - c) % 3 {
                0 => (&digests[0], &shares[0]),
                1 => (&digests[1], &shares[1]),
                _ => (&lifted.unopened[i], &third),
            };
            hasher.update(d);
            o.update_hasher(&mut hasher);
        }
    }
    let entropy = hasher.finalize();
    let mut generator = ChallengeGenerator::new(HashPRG::<H>::new(entropy.as_ref()));
    for &c in &challenges {
        let next: Party = generator.next();
        if next.index() != c {
            return Err(LiftError::FiatShamir);
        }
    }
    return Ok(LiftJournal {
        version: LIFT_JOURNAL_VERSION,
        valid: true,
        fingerprint: hash_circuit::<_, H>(&statement.circuit()),
        chain_code: statement.chain_code.clone(),
        index: statement.index,
        expected_output: y.clone(),
        binding: statement.binding.clone(),
        num_responses: n as u32,
        proof_format_id: zkboo::PROOF_FORMAT_ID,
    });
}
