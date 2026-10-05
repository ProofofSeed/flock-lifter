// SPDX-License-Identifier: LGPL-3.0-or-later

//! Succinct wrapping of a lift's chunk proofs: one Flock circuit proof, opened through an outer
//! commitment, that every chunk proof verifies.

use flock_prover::{
    challenger::FsChallenger,
    field::F128,
    lincheck::SkipPoint,
    matrix_fold::{FoldMatrix, MatrixClaim, Weight},
    pcs::OuterPcs,
    tower::{HeadEnv, RowMajorChild, WrapKey, WrapProof, parent_digest, prove_wrap, verify_wrap},
    transcript_record::RecordingChallenger,
    zerocheck::K_SKIP,
};
use pofseed_flock_lift_block::{form::CONST, program::Program};
use rayon::prelude::*;

use crate::chunk_wrap::{
    ChunkProofWrap, ChunkWrapError, chunk_params, chunk_r1cs, padded_publics, publics_digest, row_log,
    verify_chunk_with,
};

/// Phase timings of a wrap, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct WrapTimings {
    /// Verifying every chunk natively while recording its transcript, and its matrix claims.
    pub record: f64,
    /// Parsing the recorded transcripts and folding the matrix claims.
    pub tapes: f64,
    /// Building the circuit's shape.
    pub build: f64,
    /// Running the circuit's witness.
    pub witness: f64,
    /// Proving the circuit.
    pub prove: f64,
}

/// A wrapped lift: the key the wrap was built under, and the wrap proof.
pub struct Wrapped {
    /// The circuit and parameters a verifier checks the wrap under.
    pub key: WrapKey,
    /// The wrap proof.
    pub proof: WrapProof,
    /// Phase timings.
    pub timings: WrapTimings,
}

/// Why a wrap could not be made or was refused.
#[derive(Debug)]
pub enum WrapError {
    /// The chunks and their published words disagree in number, or there are none.
    Shape,
    /// A chunk proof was refused.
    Chunk(usize, ChunkWrapError),
    /// The outer circuit proof was refused.
    Outer(String),
    /// The published block digest is not the published words'.
    Digest,
    /// An accumulated matrix claim does not hold on the block's matrices.
    Matrix,
}

fn digest_words(bytes: &[u8; 32]) -> [F128; 2] {
    let w = |b: &[u8]| {
        F128::new(u64::from_le_bytes(b[..8].try_into().unwrap()), u64::from_le_bytes(b[8..].try_into().unwrap()))
    };
    return [w(&bytes[..16]), w(&bytes[16..])];
}

/// The digest a wrap publishes of its chunks' published words: the chunks' digests combined left to
/// right by the parent compression.
pub fn block_digest(program: &Program, publics: &[&[Vec<F128>]]) -> [u8; 32] {
    let digests: Vec<[u8; 32]> =
        publics.par_iter().map(|p| publics_digest(&padded_publics(p, row_log(program, p.len())))).collect();
    return digests[1..].iter().fold(digests[0], |d, s| parent_digest(&d, s));
}

/// Wraps verified chunk proofs in one circuit proof built to `env`, whose commitment `outer` opens,
/// or Ligerito when it is `None`; chunk `i` was proved over `publics[i]` under `domains[i]`.
pub fn wrap(
    program: &Program,
    publics: &[&[Vec<F128>]],
    chunks: &[ChunkProofWrap],
    domains: &[Vec<u8>],
    env: &HeadEnv,
    outer: Option<&dyn OuterPcs>,
) -> Result<Wrapped, WrapError> {
    if chunks.is_empty() || chunks.len() != publics.len() || chunks.len() != domains.len() {
        return Err(WrapError::Shape);
    }
    flock_prover::scratch::clear();
    let t = std::time::Instant::now();
    let records = chunks
        .par_iter()
        .zip(publics.par_iter())
        .zip(domains.par_iter())
        .enumerate()
        .map(|(i, ((chunk, p), domain))| {
            let mut rec = RecordingChallenger::new(FsChallenger::with_chained_blake3(domain));
            let r = verify_chunk_with(program, p, chunk, &mut rec).map_err(|e| WrapError::Chunk(i, e))?;
            let rr: Vec<F128> = r.lc_rounds.iter().rev().copied().collect();
            let skip = SkipPoint::Phi8(r.z).weights(K_SKIP);
            let dot = |alpha: F128| -> F128 {
                program
                    .comb_partial(alpha, F128::ZERO, &skip, &r.x_inner_rest, &rr)
                    .iter()
                    .zip(&r.z_partial)
                    .fold(F128::ZERO, |acc, (&x, &z)| acc + x * z)
            };
            let vb = dot(F128::ZERO);
            let va = dot(F128::ONE) + vb;
            let row = Weight::low_eq(skip.clone(), r.x_inner_rest.clone());
            let col = Weight::low_eq(r.z_partial.clone(), rr);
            let claim = |value: F128| MatrixClaim {
                row: row.clone(),
                col: col.clone(),
                value,
            };
            Ok((rec, r, [claim(va), claim(vb)]))
        })
        .collect::<Result<Vec<_>, WrapError>>()?;
    let record = t.elapsed().as_secs_f64();
    let children: Vec<RowMajorChild<'_>> = records
        .into_iter()
        .zip(chunks)
        .zip(publics)
        .zip(domains)
        .map(|((((rec, r, lc_claims), chunk), p), domain)| RowMajorChild {
            rec,
            domain: domain.clone(),
            opening: &chunk.opening,
            commitment: &chunk.commitment,
            pcs: chunk_params(program, p.len()),
            ab: r.ab,
            c: r.c,
            pd_point: r.io_point,
            rows: padded_publics(p, row_log(program, p.len())),
            lc_running: r.running,
            lc_claims,
            konst: CONST as usize,
            jagged: r.jagged,
            r1cs_digest: chunk_r1cs(program, p.len()).statement_digest(),
        })
        .collect();
    let (ma, mb) = (program.matrix(true), program.matrix(false));
    let mats: [&dyn FoldMatrix; 2] = [&ma, &mb];
    let (key, proof, tm) = prove_wrap(&children, mats, env, outer);
    flock_prover::scratch::clear();
    let timings = WrapTimings {
        record,
        tapes: tm.tapes,
        build: tm.build,
        witness: tm.witness,
        prove: tm.prove,
    };
    return Ok(Wrapped { key, proof, timings });
}

/// The serialised size of a wrap proof: the outer proof and its commitment.
pub fn proof_bytes(proof: &WrapProof) -> usize {
    return bincode::serialize(&proof.proof).expect("serialisable").len()
        + bincode::serialize(&proof.commitment).expect("serialisable").len();
}

/// Verifies a wrap proof against the published words of its chunks: the circuit proof under `key`,
/// its block digest, and the two accumulated matrix claims against the block's matrices.
pub fn verify_wrapped(
    program: &Program,
    publics: &[&[Vec<F128>]],
    key: &WrapKey,
    proof: &WrapProof,
    outer: Option<&dyn OuterPcs>,
) -> Result<(), WrapError> {
    if publics.is_empty() || key.tails.len() != publics.len() || publics.iter().any(|p| p.is_empty()) {
        return Err(WrapError::Shape);
    }
    verify_wrap(key, proof, outer).map_err(|e| WrapError::Outer(format!("{e:?}")))?;
    let at = key.block;
    if proof.public[at..at + 2] != digest_words(&block_digest(program, publics)) {
        return Err(WrapError::Digest);
    }
    for (&(at, k_col, k_row), a_side) in key.acc.iter().zip([true, false]) {
        let p = &proof.public;
        let (col, row, value) = (&p[at..at + k_col], &p[at + k_col..at + k_col + k_row], p[at + k_col + k_row]);
        if program.bilinear_eq(a_side, row, col) != value {
            return Err(WrapError::Matrix);
        }
    }
    return Ok(());
}
