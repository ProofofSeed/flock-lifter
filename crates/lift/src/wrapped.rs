// SPDX-License-Identifier: LGPL-3.0-or-later

//! The wrapped lift of a whole ZKBoo proof: chunk proofs over its responses, replaced by one wrap
//! proof whose public segment carries the words the chunks publish, with the unopened digests and
//! the verifier that checks the wrap and runs the global Fiat-Shamir gate natively.

use std::sync::Arc;

use flock_prover::{
    field::F128,
    pcs::OuterPcs,
    tower::{HeadEnv, WrapKey, WrapProof},
};
use pofseed_flock_lift_block::{native, program::Program};
use pofseed_flock_lift_statement::{LiftJournal, S};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use zkboo::prover::proof::Response;

use pofseed_flock_lift_structure::proof::StructProof;

use crate::{
    chunk_wrap::{self, ChunkProofWrap},
    lift::{LiftError, MAX_CHUNK, Statement, check_statement, gate, journal},
    root::{self, RootKey},
    wrap::{self, WrapTimings},
};

/// Version of the wrapped lift, bound into every chunk's transcript domain.
pub const WRAPPED_VERSION: &[u8] = b"pofseed-flock-lift-wrapped-v1";

/// What verifying wrapped lifts of one shape needs: the wrap circuit's key and the lift's shape.
pub struct WrappedKey {
    /// The wrap circuit's key.
    pub wrap: WrapKey,
    /// Responses per lift.
    pub responses: usize,
    /// Responses per chunk.
    pub chunk: usize,
    /// The commitment to the fixed tables of the statement's block and of the wrap circuit.
    pub root: Arc<RootKey>,
}

/// A wrapped lift.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WrappedLift {
    /// The wrap proof, whose public segment carries the published words of every response.
    pub wrap: WrapProof,
    /// The unopened view digest of every response.
    pub unopened: Vec<[u8; 32]>,
    /// The proof of what the wrap leaves about the fixed tables.
    pub structure: StructProof,
}

/// Phase timings of a wrapped lift, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct WrappedTimings {
    /// Proving the chunks.
    pub chunks: f64,
    /// Wrapping them.
    pub wrap: WrapTimings,
    /// Committing to the fixed tables, when no key was given.
    pub key: f64,
    /// Proving the structure.
    pub structure: f64,
}

/// The transcript domain of chunk `index` of a wrapped lift of `responses` responses in chunks of
/// `chunk`, over blocks of `2^k_log` bits.
///
/// The statement is no part of it: a chunk proof is bound to its statement by the block's matrices
/// and to its lift by the published words, so one wrap circuit serves every statement of a shape.
pub fn chunk_domain(k_log: usize, responses: usize, chunk: usize, index: usize) -> Vec<u8> {
    let mut d = WRAPPED_VERSION.to_vec();
    for v in [k_log, responses, chunk, index] {
        d.extend_from_slice(&(v as u64).to_le_bytes());
    }
    return d;
}

fn domains(program: &Program, responses: usize, chunk: usize) -> Vec<Vec<u8>> {
    let k_log = program.geometry().k_log();
    return (0..responses.div_ceil(chunk)).map(|i| chunk_domain(k_log, responses, chunk, i)).collect();
}

/// Lifts a ZKBoo proof of `statement` in chunks of at most `chunk` responses and wraps the chunks
/// in one proof, opened through `outer`; the fixed tables are those of `root`, or are committed at
/// rate `2^-rate` when there is none.
pub fn prove(
    program: &Arc<Program>,
    statement: &Statement,
    proof: &[Response<S, S>],
    chunk: usize,
    outer: &dyn OuterPcs,
    root: Option<Arc<RootKey>>,
    rate: usize,
) -> Result<(WrappedKey, WrappedLift, WrappedTimings), LiftError> {
    assert!((1..=MAX_CHUNK).contains(&chunk), "chunk size must be in 1..={MAX_CHUNK}");
    if proof.is_empty() {
        return Err(LiftError::Shape);
    }
    check_statement(program, statement)?;
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
    let domains = domains(program, proof.len(), chunk);
    let t = std::time::Instant::now();
    let mut chunks: Vec<ChunkProofWrap> = Vec::with_capacity(domains.len());
    for (i, ((responses, publics), domain)) in proof.chunks(chunk).zip(words.chunks(chunk)).zip(&domains).enumerate() {
        chunks.push(
            chunk_wrap::prove_chunk(program, responses, publics, domain).map_err(|e| LiftError::Witness(i * chunk, e))?,
        );
    }
    let chunks_s = t.elapsed().as_secs_f64();
    let parts: Vec<&[Vec<F128>]> = words.chunks(chunk).collect();
    let w = wrap::wrap(program, &parts, &chunks, &domains, &HeadEnv::measuring(), Some(outer)).map_err(LiftError::Wrap)?;
    let t = std::time::Instant::now();
    let root = match root {
        Some(r) if r.circuit == w.key.key.digest() && r.program == program.fingerprint() => r,
        Some(_) => return Err(LiftError::Shape),
        None => Arc::new(RootKey::new(program, &w.key, rate)),
    };
    let key_s = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    let structure = root::prove_structure(&root, &w.key, &w.proof, Some(outer)).map_err(LiftError::Wrap)?;
    let timings = WrappedTimings {
        chunks: chunks_s,
        wrap: w.timings,
        key: key_s,
        structure: t.elapsed().as_secs_f64(),
    };
    let key = WrappedKey {
        wrap: w.key,
        responses: proof.len(),
        chunk,
        root,
    };
    return Ok((key, WrappedLift { wrap: w.proof, unopened, structure }, timings));
}

/// The published words of every response of a wrapped lift, read from its public segment.
pub fn words(program: &Program, key: &WrappedKey, lifted: &WrappedLift) -> Option<Vec<Vec<F128>>> {
    let n_io = program.geometry().io_word_cols().len();
    let width = pofseed_flock_lift_block::layout::IO_WORDS;
    let mut out = Vec::with_capacity(key.responses);
    for i in 0..key.responses.div_ceil(key.chunk) {
        let live = key.chunk.min(key.responses - i * key.chunk);
        let (at, len) = wrap::words_at(&key.wrap, i);
        let rows = lifted.wrap.public.get(at..at + len)?;
        if len != width << chunk_wrap::row_log(program, live) {
            return None;
        }
        out.extend(rows.chunks(width).take(live).map(|r| r[..n_io].to_vec()));
    }
    return Some(out);
}

/// Verifies a wrapped lift of `statement` under `key`, opened through `outer`, returning the
/// journal it attests.
pub fn verify(
    program: &Program,
    key: &WrappedKey,
    statement: &Statement,
    lifted: &WrappedLift,
    outer: &dyn OuterPcs,
) -> Result<LiftJournal, LiftError> {
    if key.root.program != program.fingerprint() {
        return Err(LiftError::Statement);
    }
    check_statement(program, statement)?;
    if lifted.unopened.len() != key.responses || key.wrap.tails.len() != key.responses.div_ceil(key.chunk) {
        return Err(LiftError::Shape);
    }
    let words = words(program, key, lifted).ok_or(LiftError::Shape)?;
    let parts: Vec<&[Vec<F128>]> = words.chunks(key.chunk).collect();
    root::verify_root(&key.root.verifying(), &key.wrap, &lifted.wrap, &lifted.structure, Some(outer)).map_err(LiftError::Wrap)?;
    wrap::check_words(program, &parts, &key.wrap, &lifted.wrap).map_err(LiftError::Wrap)?;
    gate(program, statement, &words, &lifted.unopened)?;
    return Ok(journal(statement, key.responses));
}
