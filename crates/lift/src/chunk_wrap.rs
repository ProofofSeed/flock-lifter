// SPDX-License-Identifier: LGPL-3.0-or-later

//! A row-major Flock proof over a batch of response blocks in the form a wrap circuit verifies:
//! its transcript runs on chained BLAKE3, its published words enter the transcript as a digest
//! and are bound by a packed-direct claim, and its claims are opened through Flock's merged
//! transport on one full-height column.

use std::sync::Arc;

use flock_prover::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    lincheck::{
        LincheckCircuit, LincheckClaim, LincheckError, LincheckGrinding, LincheckProof, QuirkyPoint, SkipPoint,
        build_eq_table,
    },
    matrix_fold::JaggedAssertion,
    merkle::HashKind,
    pcs::{
        Commitment, DirectEqInd, MergedOpenProof, PackedDirectClaim, PackedDirectClaimRef, PcsParams,
        ligerito::{LigeritoProfile, embedded_initial_k_or_default},
        open_batch_merged, verify_batch_merged_deferred,
    },
    proof::{ZClaim, bind_statement},
    prover::{ProveCore, prove_fast_core},
    r1cs::BlockR1cs,
    zerocheck::{K_SKIP, ZerocheckProof, verify_with_grinding as verify_zerocheck},
};
use pofseed_flock_lift_block::{
    layout::{IO_BASE_WORD, IO_WORDS},
    program::{Program, WitnessError},
};
use pofseed_flock_lift_statement::S;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use zkboo::prover::proof::Response;

use crate::chunk_rm::{profile, r1cs_for};

/// The smallest chunk committed, as a log of bits.
pub const MIN_M: usize = 28;

/// log2 of the published words of a row.
const IO_WORDS_LOG: usize = IO_WORDS.trailing_zeros() as usize;

/// A wrap-form chunk proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChunkProofWrap {
    /// The zerocheck proof.
    pub zerocheck: ZerocheckProof,
    /// The lincheck proof.
    pub lincheck: LincheckProof,
    /// The merged opening of the zerocheck, lincheck and published-word claims.
    pub opening: MergedOpenProof,
    /// The witness commitment.
    pub commitment: Commitment,
}

/// What a chunk's verification binds, as a wrap circuit consumes it.
#[derive(Clone, Debug)]
pub struct ChunkReplay {
    /// The lincheck's claim on the witness.
    pub ab: ZClaim,
    /// The zerocheck's claim on the witness.
    pub c: ZClaim,
    /// The published-word claim's point.
    pub io_point: Vec<F128>,
    /// The published-word claim's value.
    pub io_value: F128,
    /// The zerocheck's skip challenge.
    pub z: F128,
    /// The lincheck's row point within a row, after the skipped variables.
    pub x_inner_rest: Vec<F128>,
    /// The lincheck's round challenges, in round order.
    pub lc_rounds: Vec<F128>,
    /// The lincheck's partial witness evaluations.
    pub z_partial: Vec<F128>,
    /// The lincheck's final running claim.
    pub running: F128,
    /// The merged opening's layout claims.
    pub jagged: JaggedAssertion,
}

/// Why a wrap-form chunk proof was refused.
#[derive(Debug)]
pub enum ChunkWrapError {
    /// A block's published words have the wrong length, or there are none.
    PublicLength,
    /// The zerocheck or the lincheck refused.
    Core(String),
    /// The merged opening refused.
    Opening,
}

/// log2 of the rows a chunk of `count` responses commits.
pub fn row_log(program: &Program, count: usize) -> usize {
    let floor = MIN_M.saturating_sub(program.geometry().k_log());
    return (count.next_power_of_two().trailing_zeros() as usize).max(3).max(floor);
}

/// The commitment parameters of a chunk committing `2^m` bits under `profile`.
pub fn pcs_params_for(m: usize, profile: LigeritoProfile) -> PcsParams {
    return PcsParams {
        m,
        log_inv_rate: profile.log_inv_rate(),
        log_batch_size: embedded_initial_k_or_default(m, profile),
        profile,
        num_lanes: None,
        merkle_hash: HashKind::Blake3,
    };
}

/// The commitment parameters of a chunk of `count` responses.
pub fn chunk_params(program: &Program, count: usize) -> PcsParams {
    return pcs_params_for(program.geometry().k_log() + row_log(program, count), profile());
}

/// The Flock statement of a chunk of `count` responses.
pub fn chunk_r1cs(program: &Program, count: usize) -> BlockR1cs {
    return r1cs_for(program, row_log(program, count));
}

/// The published words of every row of a chunk, each padded to the published subcube, the last
/// live row repeated as padding.
pub fn padded_publics(publics: &[Vec<F128>], nu: usize) -> Vec<Vec<F128>> {
    return (0..1usize << nu)
        .map(|j| {
            let mut row = publics[j.min(publics.len() - 1)].clone();
            row.resize(IO_WORDS, F128::ZERO);
            row
        })
        .collect();
}

/// The digest of the published words of every row, in row order.
pub fn publics_digest(rows: &[Vec<F128>]) -> [u8; 32] {
    let words: Vec<F128> = rows.iter().flatten().copied().collect();
    return flock_prover::union::publics_digest(&words);
}

fn observe_publics<Ch: Challenger>(challenger: &mut Ch, rows: &[Vec<F128>]) {
    challenger.observe_label(b"pofseed-flock-lift-published-words");
    challenger.observe_bytes(&publics_digest(rows));
}

/// The claim binding the published words of every row: their multilinear extension at a transcript
/// point whose word coordinates beyond the published subcube are its base.
fn io_claim<Ch: Challenger>(challenger: &mut Ch, rows: &[Vec<F128>], k_log: usize, nu: usize) -> (Vec<F128>, F128) {
    let r_word: Vec<F128> = (0..IO_WORDS_LOG).map(|_| challenger.sample_f128()).collect();
    let x_outer: Vec<F128> = (0..nu).map(|_| challenger.sample_f128()).collect();
    let mut point = r_word.clone();
    point.extend((IO_WORDS_LOG..k_log - 7).map(|j| if (IO_BASE_WORD >> j) & 1 == 1 { F128::ONE } else { F128::ZERO }));
    point.extend_from_slice(&x_outer);
    let e_word = build_eq_table(&r_word);
    let e_row = build_eq_table(&x_outer);
    let value = rows
        .par_iter()
        .zip(e_row.par_iter())
        .map(|(row, &e)| e * row.iter().zip(&e_word).fold(F128::ZERO, |a, (&w, &c)| a + c * w))
        .reduce(|| F128::ZERO, |x, y| x + y);
    return (point, value);
}

/// The column heights and row variables the merged opening lays a chunk's `2^(m−7)` words out as:
/// one full-height column.
fn opening_layout(m: usize) -> (Vec<u64>, usize) {
    return (vec![1u64 << (m - 7)], m - 7);
}

/// The lincheck's byte stripes of a row-major witness.
fn lincheck_stripe(z: &[F128], nu: usize, k_log: usize) -> Vec<u8> {
    let k = 1usize << k_log;
    let row_words = k / 64;
    // SAFETY: `F128` is `repr(C)` over two `u64`s, `lo` then `hi`.
    let words: &[u64] = unsafe { std::slice::from_raw_parts(z.as_ptr() as *const u64, z.len() * 2) };
    let mut out = vec![0u8; (k << nu) / 8];
    const SPAN: usize = 1 << 12;
    out.par_chunks_mut(SPAN * 64).enumerate().for_each(|(c, chunk)| {
        for (i, bytes) in chunk.chunks_mut(64).enumerate() {
            let g = c * SPAN + i;
            let (stripe, w) = (g / row_words, g % row_words);
            let lanes: [u64; 8] = std::array::from_fn(|r| words[(8 * stripe + r) * row_words + w]);
            flock_prover::bits::transpose_8_u64s_to_64_bytes(&lanes, bytes);
        }
    });
    return out;
}

#[derive(Clone, Copy)]
struct SendPtr(*mut F128);

unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}

/// Proves a batch of responses whose published words are `publics`.
pub fn prove_chunk(
    program: &Arc<Program>,
    responses: &[Response<S, S>],
    publics: &[Vec<F128>],
    domain: &[u8],
) -> Result<ChunkProofWrap, WitnessError> {
    assert!(!responses.is_empty() && responses.len() == publics.len());
    for response in responses {
        program.check_response(response)?;
    }
    let timing = std::env::var_os("POFSEED_TIMING").is_some();
    let t = std::time::Instant::now();
    let nu = row_log(program, responses.len());
    let k_log = program.geometry().k_log();
    let r1cs = r1cs_for(program, nu);
    let params = pcs_params_for(r1cs.m, profile());
    let block_words = 1usize << (k_log - 7);
    let total = block_words << nu;
    let mut bufs = [(); 3].map(|_| flock_prover::alloc_zeroed_vec::<F128>(total));
    let ptrs = bufs.each_mut().map(|b| SendPtr(b.as_mut_ptr()));
    (0..1usize << nu).into_par_iter().for_each(|j| {
        let response = &responses[j.min(responses.len() - 1)];
        let words = program.block_bits() / 64;
        let mut local = [vec![0u64; words], vec![0u64; words], vec![0u64; words]];
        let [lz, la, lb] = &mut local;
        program.write_witness(response, lz, la, lb).expect("responses were checked");
        for (ptr, buf) in ptrs.iter().zip(local.iter()) {
            for c in 0..block_words {
                // SAFETY: row `j` owns words `[j·block_words, (j+1)·block_words)`.
                unsafe {
                    *ptr.0.add((j << (k_log - 7)) + c) = F128::new(buf[2 * c], buf[2 * c + 1]);
                }
            }
        }
    });
    let [z, a, b] = bufs;
    let stripe = lincheck_stripe(&z, nu, k_log);
    if timing {
        eprintln!("[pofseed] wrap-form witness and stripe {:.2} s", t.elapsed().as_secs_f64());
    }
    let rows = padded_publics(publics, nu);
    let mut challenger = FsChallenger::with_chained_blake3(domain);
    observe_publics(&mut challenger, &rows);
    let t = std::time::Instant::now();
    let core: ProveCore =
        prove_fast_core(&r1cs, &params, z, a, b, stripe, program.as_ref() as &dyn LincheckCircuit, &mut challenger);
    if timing {
        eprintln!("[pofseed] wrap-form commit, zerocheck and lincheck {:.2} s", t.elapsed().as_secs_f64());
    }
    let t = std::time::Instant::now();
    let io = io_claim(&mut challenger, &rows, k_log, nu);
    let lig = params.ligerito_prover_config().expect("registered Ligerito configuration");
    let padding = r1cs.padding_spec();
    let x_fulls: Vec<Vec<F128>> = [&core.ab, &core.c]
        .iter()
        .map(|claim| [claim.point.x_inner_rest.as_slice(), claim.point.x_outer.as_slice()].concat())
        .collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(|x| x.as_slice()).collect();
    let (heights, n_log) = opening_layout(r1cs.m);
    let opening = open_batch_merged(
        core.z_packed,
        None,
        &core.prover_data,
        &core.commitment,
        &x_refs,
        &[core.s_hat_v_ab.as_deref(), Some(core.s_hat_v_c.as_slice())],
        &[None, None],
        &[PackedDirectClaim {
            eq_ind: DirectEqInd::EqPoint(io.0.clone()),
            point: io.0,
            value: io.1,
        }],
        &padding,
        &heights,
        n_log,
        &lig,
        params.opening_grinding(),
        None,
        &mut challenger,
    );
    if timing {
        eprintln!("[pofseed] wrap-form opening {:.2} s", t.elapsed().as_secs_f64());
    }
    return Ok(ChunkProofWrap {
        zerocheck: core.zc_proof,
        lincheck: core.lc_proof,
        opening,
        commitment: core.commitment,
    });
}

/// Replays Flock's lincheck verifier, evaluating its final equation from the block's structure.
fn verify_lincheck<Ch: Challenger>(
    program: &Program,
    k_log: usize,
    x_ab: &QuirkyPoint,
    v_a: F128,
    v_b: F128,
    proof: &LincheckProof,
    grinding: LincheckGrinding,
    challenger: &mut Ch,
) -> Result<(LincheckClaim, F128), LincheckError> {
    let inner_rest_len = k_log - K_SKIP;
    let n_skip = 1usize << K_SKIP;
    if x_ab.x_inner_rest.len() != inner_rest_len {
        return Err(LincheckError::BadInnerRestLength {
            which: "x_ab",
            expected: inner_rest_len,
            got: x_ab.x_inner_rest.len(),
        });
    }
    if proof.rounds.len() != inner_rest_len {
        return Err(LincheckError::BadVectorLength {
            which: "rounds",
            expected: inner_rest_len,
            got: proof.rounds.len(),
        });
    }
    if proof.z_partial.len() != n_skip {
        return Err(LincheckError::BadVectorLength {
            which: "z_partial",
            expected: n_skip,
            got: proof.z_partial.len(),
        });
    }
    let expected_nonces = grinding.nonce_count(inner_rest_len, 1, K_SKIP);
    if proof.grinding_nonces.len() != expected_nonces {
        return Err(LincheckError::BadGrindingNonceCount {
            expected: expected_nonces,
            got: proof.grinding_nonces.len(),
        });
    }
    challenger.observe_label(b"flock-lincheck-v0");
    let mut nonce = 0;
    let ground = |challenger: &mut Ch, bits: Option<u32>, which, nonce: &mut usize| match bits {
        Some(bits) => {
            let r = challenger
                .verify_pow_and_sample_f128(proof.grinding_nonces[*nonce], bits)
                .ok_or(LincheckError::InvalidGrindingNonce { which })?;
            *nonce += 1;
            Ok(r)
        }
        None => Ok(challenger.sample_f128()),
    };
    let alpha = ground(challenger, grinding.alpha_bits(), "alpha", &mut nonce)?;
    let beta = ground(challenger, grinding.beta_bits(), "beta", &mut nonce)?;
    let mut running = alpha * v_a + v_b + beta;
    let mut r_rounds = Vec::with_capacity(inner_rest_len);
    for &(e1, e_inf) in &proof.rounds {
        challenger.observe_f128(e1);
        challenger.observe_f128(e_inf);
        let r = ground(challenger, grinding.multilinear_round_bits(), "sumcheck-round", &mut nonce)?;
        let e0 = running + e1;
        let c1 = e0 + e1 + e_inf;
        running = e_inf * r * r + c1 * r + e0;
        r_rounds.push(r);
    }
    challenger.observe_f128_slice(&proof.z_partial);
    r_rounds.reverse();
    let skip = x_ab.z_skip.weights(K_SKIP);
    let comb = program.comb_partial(alpha, beta, &skip, &x_ab.x_inner_rest, &r_rounds);
    let paired = comb.iter().zip(&proof.z_partial).fold(F128::ZERO, |acc, (&c, &z)| acc + c * z);
    if paired != running {
        return Err(LincheckError::ConsistencyFailed {
            which: "sumcheck-final",
        });
    }
    let r_inner_skip = match &x_ab.z_skip {
        SkipPoint::Phi8(_) => match grinding.skip_bits(K_SKIP) {
            Some(bits) => SkipPoint::Phi8(ground(challenger, Some(bits), "inner-skip", &mut nonce)?),
            None => x_ab.z_skip.sample_fresh(challenger),
        },
        SkipPoint::Ag(_) => return Err(LincheckError::InvalidGrindingNonce { which: "inner-skip" }),
    };
    let lambda = r_inner_skip.weights(K_SKIP);
    let w = lambda.iter().zip(&proof.z_partial).fold(F128::ZERO, |acc, (&l, &z)| acc + l * z);
    return Ok((
        LincheckClaim {
            r_inner_skip,
            r_inner_rest: r_rounds,
            w,
        },
        running,
    ));
}

/// Verifies a chunk proof against the published words of its blocks.
pub fn verify_chunk(
    program: &Program,
    publics: &[Vec<F128>],
    chunk: &ChunkProofWrap,
    domain: &[u8],
) -> Result<(), ChunkWrapError> {
    let mut challenger = FsChallenger::with_chained_blake3(domain);
    return verify_chunk_with(program, publics, chunk, &mut challenger).map(|_| ());
}

/// Verifies a chunk proof on a given transcript, returning what its verification binds.
pub fn verify_chunk_with<Ch: Challenger>(
    program: &Program,
    publics: &[Vec<F128>],
    chunk: &ChunkProofWrap,
    challenger: &mut Ch,
) -> Result<ChunkReplay, ChunkWrapError> {
    let n_io = program.geometry().io_word_cols().len();
    if publics.is_empty() || publics.iter().any(|p| p.len() != n_io) {
        return Err(ChunkWrapError::PublicLength);
    }
    let nu = row_log(program, publics.len());
    if publics.len() > 1 << nu {
        return Err(ChunkWrapError::PublicLength);
    }
    let k_log = program.geometry().k_log();
    let r1cs = r1cs_for(program, nu);
    let params = pcs_params_for(r1cs.m, profile());
    let rows = padded_publics(publics, nu);
    observe_publics(challenger, &rows);
    bind_statement(challenger, &r1cs, &chunk.commitment);
    let zc = verify_zerocheck(r1cs.m, &chunk.zerocheck, params.zerocheck_grinding(), challenger)
        .map_err(|e| ChunkWrapError::Core(format!("{e:?}")))?;
    let x_ab = r1cs.x_ab_from_multilinear_values(SkipPoint::Phi8(zc.z), &zc.mlv_challenges);
    let (lc, running) = verify_lincheck(
        program,
        k_log,
        &x_ab,
        zc.a_eval,
        zc.b_eval,
        &chunk.lincheck,
        params.lincheck_grinding(),
        challenger,
    )
    .map_err(|e| ChunkWrapError::Core(format!("{e:?}")))?;
    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc.r_inner_skip, &lc.r_inner_rest, &x_ab.x_outer),
        value: lc.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(SkipPoint::Phi8(zc.z), &zc.r_rest),
        value: zc.c_eval,
    };
    let io = io_claim(challenger, &rows, k_log, nu);
    let claims = [ab, c];
    let x_fulls: Vec<Vec<F128>> =
        claims.iter().map(|z| [z.point.x_inner_rest.as_slice(), z.point.x_outer.as_slice()].concat()).collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(Vec::as_slice).collect();
    let (heights, n_log) = opening_layout(r1cs.m);
    let jagged = verify_batch_merged_deferred(
        &chunk.commitment,
        &claims.iter().map(|z| z.value).collect::<Vec<_>>(),
        &claims.iter().map(|z| z.point.z_skip).collect::<Vec<_>>(),
        &x_refs,
        &[PackedDirectClaimRef {
            point: &io.0,
            value: io.1,
        }],
        &heights,
        n_log,
        &chunk.opening,
        &params.ligerito_verifier_config().map_err(|_| ChunkWrapError::Opening)?,
        params.opening_grinding(),
        None,
        challenger,
    )
    .map_err(|_| ChunkWrapError::Opening)?;
    let [ab, c] = claims;
    return Ok(ChunkReplay {
        ab,
        c,
        io_point: io.0,
        io_value: io.1,
        z: zc.z,
        x_inner_rest: x_ab.x_inner_rest.clone(),
        lc_rounds: lc.r_inner_rest.iter().rev().copied().collect(),
        z_partial: chunk.lincheck.z_partial.clone(),
        running,
        jagged,
    });
}
