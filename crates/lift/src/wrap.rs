// SPDX-License-Identifier: LGPL-3.0-or-later

//! Succinct wrapping of a lift's chunk proofs: one Flock circuit proof, opened through an outer
//! commitment, that every chunk proof verifies.

use flock_prover::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    lincheck::SkipPoint,
    matrix_fold::{FoldMatrix, MatrixClaim, Weight},
    pcs::OuterPcs,
    tower::{HeadEnv, RowMajorChild, WrapKey, WrapProof, prove_wrap_on},
    transcript_record::RecordingChallenger,
    zerocheck::K_SKIP,
};
use pofseed_flock_lift_block::{form::CONST, program::Program};
use rayon::prelude::*;

use crate::{
    chunk_wrap::{
        ChunkProofWrap, ChunkWrapError, chunk_params, chunk_r1cs, padded_publics, row_log, verify_chunk_with,
    },
    transcript::KeccakChallenger,
};

/// The transcript domain of a wrap's outer proof.
pub const WRAP_DOMAIN: &[u8] = b"pofseed-flock-lift-wrap-v1";

/// The name under which a wrap's key locates a chunk's published words in the public segment.
const WORDS_TAIL: &str = "published words";

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
    /// The published words are not the given ones.
    Words,
    /// An accumulated matrix claim does not hold on the block's matrices.
    Matrix,
    /// An element table's reported evaluation is not the table's.
    Element,
    /// The structure proof was refused.
    Structure(pofseed_flock_lift_structure::proof::StructError),
}

/// A wrap's outer transcript, bound to the circuit's public segment.
pub fn outer_transcript(public: &[F128]) -> KeccakChallenger {
    let mut ch = KeccakChallenger::new(WRAP_DOMAIN);
    bind_public(public, &mut ch);
    return ch;
}

fn bind_public(public: &[F128], ch: &mut KeccakChallenger) {
    ch.observe_label(b"pofseed-flock-lift-wrap-public");
    ch.observe_f128_slice(public);
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
            publish_rows: true,
        })
        .collect();
    let (ma, mb) = (program.matrix(true), program.matrix(false));
    let mats: [&dyn FoldMatrix; 2] = [&ma, &mb];
    let (key, proof, tm) =
        prove_wrap_on(&children, mats, env, outer, &mut KeccakChallenger::new(WRAP_DOMAIN), bind_public);
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

/// Where chunk `i`'s published words sit in a wrap's public segment.
pub fn words_at(key: &WrapKey, i: usize) -> (usize, usize) {
    let (_, at, len) = key.tails[i].iter().find(|(name, _, _)| *name == WORDS_TAIL).expect("a wrap publishes its words");
    return (*at, *len);
}

/// The two accumulated matrix claims a wrap publishes, on `A` then `B`: the row point, the column
/// point and the value.
pub fn matrix_claims(key: &WrapKey, proof: &WrapProof) -> [(Vec<F128>, Vec<F128>, F128); 2] {
    return [0, 1].map(|i| {
        let (at, k_col, k_row) = key.acc[i];
        let p = &proof.public;
        (p[at + k_col..at + k_col + k_row].to_vec(), p[at..at + k_col].to_vec(), p[at + k_col + k_row])
    });
}

/// Verifies a wrap proof against the published words of its chunks: the circuit proof under `key`,
/// the words it publishes, and the two accumulated matrix claims against the block's matrices.
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
    key.key
        .verify_on(proof, outer, &mut outer_transcript(&proof.public))
        .map_err(|e| WrapError::Outer(format!("{e:?}")))?;
    // Flock's verifier takes the element tables' evaluations from the proof; the claims pass checks them.
    let table_of = vec![0; key.key.shape.registry.num_boolean()];
    crate::root::outer_claims(key, &table_of, proof, outer)?;
    check_words(program, publics, key, proof)?;
    for ((row, col, value), a_side) in matrix_claims(key, proof).into_iter().zip([true, false]) {
        if program.bilinear_eq(a_side, &row, &col) != value {
            return Err(WrapError::Matrix);
        }
    }
    return Ok(());
}

/// Checks that the words a wrap publishes are the given ones, padded as its chunks pad them.
pub fn check_words(program: &Program, publics: &[&[Vec<F128>]], key: &WrapKey, proof: &WrapProof) -> Result<(), WrapError> {
    if key.tails.len() != publics.len() {
        return Err(WrapError::Shape);
    }
    for (i, p) in publics.iter().enumerate() {
        let (at, len) = words_at(key, i);
        let words: Vec<F128> = padded_publics(p, row_log(program, p.len())).into_iter().flatten().collect();
        if words.len() != len || proof.public[at..at + len] != words[..] {
            return Err(WrapError::Words);
        }
    }
    return Ok(());
}
