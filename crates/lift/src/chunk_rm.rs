// SPDX-License-Identifier: LGPL-3.0-or-later

//! A Flock proof over a batch of response blocks through the single-table row-major path, with
//! the published words bound by one extra evaluation claim on the committed witness.

use std::sync::{Arc, OnceLock};

use flock_prover::{
    challenger::Challenger,
    field::F128,
    merkle::HashKind,
    lincheck::{
        LincheckCircuit, LincheckClaim, LincheckError, LincheckGrinding, LincheckProof, QuirkyPoint,
        SkipPoint, pack_z_lincheck_from_packed,
    },
    pcs::{
        Commitment, PcsParams,
        ligerito::{LigeritoProfile, embedded_initial_k_or_default},
        open_batch_mixed_ligerito_with_precomputed_s_hat_v_and_grinding,
    },
    proof::{ZClaim, bind_statement},
    prover::{ProveCore, prove_fast_core},
    r1cs::{BlockR1cs, SparseBinaryMatrix, WitnessLayout},
    verifier::{FlockVerifyError, verify_claims_ligerito},
    zerocheck::{K_SKIP, verify_with_grinding as verify_zerocheck_with_grinding},
};
use pofseed_flock_lift_block::{
    layout::{IO_BASE_WORD, IO_WORDS},
    program::{Program, WitnessError},
};
use pofseed_flock_lift_statement::S;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use zkboo::prover::proof::Response;

use crate::{matrix::ExplicitClaim, transcript::KeccakChallenger};

/// The Ligerito profile every chunk is proved under: `Fast` (rate 1/2) unless
/// `POFSEED_LIGERITO_PROFILE` selects `slim` (rate 1/4) or `secure` (the unique-decoding regime).
///
/// Prover and verifier read it independently, and a disagreement is refused rather than
/// misverified: the profile is part of the committed parameters, which the opening compares.
pub fn profile() -> LigeritoProfile {
    return match std::env::var("POFSEED_LIGERITO_PROFILE").as_deref() {
        Ok("slim") => LigeritoProfile::Slim,
        Ok("secure") => LigeritoProfile::Secure,
        Ok("fast") | Err(_) => LigeritoProfile::Fast,
        Ok(other) => panic!("unknown Ligerito profile {other}"),
    };
}

/// A row-major Flock proof over a batch of response blocks.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ChunkProofRm {
    /// The zerocheck proof.
    pub zerocheck: flock_prover::zerocheck::ZerocheckProof,
    /// The lincheck proof.
    pub lincheck: flock_prover::lincheck::LincheckProof,
    /// The batched opening of the zerocheck, lincheck and published-word claims.
    pub opening: flock_prover::pcs::BatchOpeningProofLigerito,
    /// The witness commitment.
    pub commitment: Commitment,
}

/// Why a row-major chunk proof was refused.
#[derive(Debug)]
pub enum ChunkRmError {
    /// A block's published words have the wrong length, or there are none.
    PublicLength,
    /// Flock's zerocheck or lincheck refused the proof.
    Core(FlockVerifyError),
    /// The batched opening was refused.
    Opening,
}

fn row_log(count: usize) -> usize {
    return (count.next_power_of_two().trailing_zeros() as usize).max(3);
}

fn r1cs_for(program: &Program, nu: usize) -> BlockR1cs {
    let stub = || SparseBinaryMatrix::new(0, 0, Vec::new());
    let k_log = program.geometry().k_log();
    return BlockR1cs {
        m: k_log + nu,
        k_log,
        k_skip: K_SKIP,
        useful_bits: 1 << k_log,
        a_0: stub(),
        b_0: stub(),
        c_0: stub(),
        layout: WitnessLayout::RowMajor,
        const_pin: Some(0),
        digest_cache: OnceLock::new(),
        csc_cache: OnceLock::new(),
    };
}

/// The digest of the Flock statement a chunk of `2^nu` blocks is bound to.
pub fn statement_digest(program: &Program, nu: usize) -> [u8; 32] {
    return r1cs_for(program, nu).statement_digest();
}

/// The PCS parameters a chunk committing `2^m` bits is proved and verified under.
pub fn pcs_params(m: usize) -> PcsParams {
    return pcs_params_for(m, profile());
}

/// The PCS parameters of a chunk committing `2^m` bits under `profile`.
pub fn pcs_params_for(m: usize, profile: LigeritoProfile) -> PcsParams {
    return PcsParams {
        m,
        log_inv_rate: profile.log_inv_rate(),
        log_batch_size: embedded_initial_k_or_default(m, profile),
        profile,
        num_lanes: None,
        merkle_hash: HashKind::Sha256,
    };
}

/// The published words of every row: the live rows', then copies of the last live row's.
fn padded_publics(publics: &[Vec<F128>], nu: usize) -> Vec<Vec<F128>> {
    let mut rows = publics.to_vec();
    rows.resize(1 << nu, publics[publics.len() - 1].clone());
    return rows;
}

fn observe_publics<Ch: Challenger>(challenger: &mut Ch, publics: &[Vec<F128>]) {
    challenger.observe_label(b"pofseed-flock-lift-published-words");
    for row in publics {
        for &w in row {
            challenger.observe_f128(w);
        }
    }
}

/// The evaluation claim binding the published-word subcube of every row, at a point sampled
/// from the transcript, with its value computed from the published words.
fn io_claim<Ch: Challenger>(challenger: &mut Ch, rows: &[Vec<F128>], k_log: usize, nu: usize) -> ZClaim {
    let z_skip = SkipPoint::Phi8(challenger.sample_f128());
    let r6 = challenger.sample_f128();
    let r_word: Vec<F128> = (0..4).map(|_| challenger.sample_f128()).collect();
    let x_outer: Vec<F128> = (0..nu).map(|_| challenger.sample_f128()).collect();
    let mut x_inner_rest = Vec::with_capacity(k_log - K_SKIP);
    x_inner_rest.push(r6);
    x_inner_rest.extend_from_slice(&r_word);
    for bit in 11..k_log {
        let set = ((IO_BASE_WORD * 128) >> bit) & 1 == 1;
        x_inner_rest.push(if set { F128::ONE } else { F128::ZERO });
    }
    let eq = |r: &[F128]| -> Vec<F128> {
        let mut t = vec![F128::ONE];
        for &x in r {
            t = t.iter().flat_map(|&e| [e * (F128::ONE + x), e * x]).collect();
            let half = t.len() / 2;
            let mut ordered = vec![F128::ZERO; t.len()];
            for i in 0..half {
                ordered[i] = t[2 * i];
                ordered[i + half] = t[2 * i + 1];
            }
            t = ordered;
        }
        return t;
    };
    let skip = z_skip.weights(K_SKIP);
    let bit_w: Vec<F128> = (0..128)
        .map(|b| skip[b & 63] * if b >> 6 == 0 { F128::ONE + r6 } else { r6 })
        .collect();
    let e_word = eq(&r_word);
    let e_row = eq(&x_outer);
    let mut value = F128::ZERO;
    for (j, row) in rows.iter().enumerate() {
        for w in 0..IO_WORDS {
            let word = row.get(w).copied().unwrap_or(F128::ZERO);
            let mut acc = F128::ZERO;
            for (b, &bw) in bit_w.iter().enumerate() {
                let bit = if b < 64 { (word.lo >> b) & 1 } else { (word.hi >> (b - 64)) & 1 };
                if bit == 1 {
                    acc += bw;
                }
            }
            value += e_row[j] * e_word[w] * acc;
        }
    }
    return ZClaim {
        point: QuirkyPoint {
            z_skip,
            x_inner_rest,
            x_outer,
        },
        value,
    };
}

#[cfg(feature = "count")]
mod count {
    use flock_prover::{challenger::fs_count, field::gf2_128::op_count, merkle::hash_count};

    /// Cumulative verifier arithmetic and hashing counters at one instant.
    pub struct Counts {
        muls: u64,
        invs: u64,
        leaf_compressions: u64,
        pairs: u64,
        squeezes: u64,
        pow: u64,
    }

    impl Counts {
        /// The counters now.
        pub fn now() -> Self {
            let m = op_count::snapshot();
            let (_, leaf_compressions, pairs) = hash_count::snapshot();
            let (squeezes, _, pow) = fs_count::snapshot();
            return Self {
                muls: m.muls_excluding_inv(),
                invs: m.invs,
                leaf_compressions,
                pairs,
                squeezes,
                pow,
            };
        }

        /// Prints what was counted between `earlier` and this instant.
        pub fn report_since(&self, earlier: &Counts, label: &str) {
            eprintln!(
                "[count] {label}: F128 muls {}, inversions {}, SHA-256 compressions {} (leaves) + {} (pairs × 2), PoW checks {}, transcript squeezes {}",
                self.muls - earlier.muls,
                self.invs - earlier.invs,
                self.leaf_compressions - earlier.leaf_compressions,
                2 * (self.pairs - earlier.pairs),
                self.pow - earlier.pow,
                self.squeezes - earlier.squeezes,
            );
        }
    }
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
) -> Result<ChunkProofRm, WitnessError> {
    assert!(!responses.is_empty() && responses.len() == publics.len());
    for response in responses {
        program.check_response(response)?;
    }
    let timing = std::env::var_os("POFSEED_TIMING").is_some();
    let t = std::time::Instant::now();
    let nu = row_log(responses.len());
    let k_log = program.geometry().k_log();
    let r1cs = r1cs_for(program, nu);
    let params = pcs_params(r1cs.m);
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
    let stripe = pack_z_lincheck_from_packed(&z, r1cs.m, k_log);
    if timing {
        eprintln!("[pofseed] row-major witness and stripe {:.2} s", t.elapsed().as_secs_f64());
    }
    let rows = padded_publics(publics, nu);
    let mut challenger = KeccakChallenger::new(domain);
    observe_publics(&mut challenger, &rows);
    let t = std::time::Instant::now();
    let core: ProveCore = prove_fast_core(&r1cs, &params, z, a, b, stripe, program.as_ref() as &dyn LincheckCircuit, &mut challenger);
    if timing {
        eprintln!("[pofseed] row-major commit, zerocheck and lincheck {:.2} s", t.elapsed().as_secs_f64());
    }
    let t = std::time::Instant::now();
    let io = io_claim(&mut challenger, &rows, k_log, nu);
    let lig_config = params.ligerito_prover_config().expect("registered Ligerito configuration");
    let padding = r1cs.padding_spec();
    let x_fulls: Vec<Vec<F128>> = [&core.ab, &core.c, &io]
        .iter()
        .map(|claim| {
            let mut x = claim.point.x_inner_rest.clone();
            x.extend_from_slice(&claim.point.x_outer);
            x
        })
        .collect();
    let x_refs: Vec<&[F128]> = x_fulls.iter().map(|x| x.as_slice()).collect();
    let opening = open_batch_mixed_ligerito_with_precomputed_s_hat_v_and_grinding(
        core.z_packed,
        &core.prover_data,
        &core.commitment,
        &x_refs,
        &[core.s_hat_v_ab.as_deref(), Some(core.s_hat_v_c.as_slice()), None],
        &[],
        &padding,
        &lig_config,
        params.opening_grinding(),
        &mut challenger,
    );
    if timing {
        eprintln!("[pofseed] row-major opening {:.2} s", t.elapsed().as_secs_f64());
    }
    return Ok(ChunkProofRm {
        zerocheck: core.zc_proof,
        lincheck: core.lc_proof,
        opening,
        commitment: core.commitment,
    });
}

/// Replays Flock's lincheck verifier over the same transcript, discharging its final equation
/// from the block's structure instead of from a vector over the block's columns.
///
/// Flock's own verifier materialises the row weight at every one of the block's `2^k_log`
/// columns, asks the circuit to fold the matrices there, and then binds that vector down one
/// sumcheck variable at a time — three passes over the block width, and at `k_log = 28` a
/// multi-gigabyte allocation. Nothing in the sumcheck replay needs the vector until its last
/// equation, so this walks the transcript identically, keeps only the running claim, and
/// evaluates the folded combination at the end through [`Program::comb_partial`].
///
/// The transcript is Flock's, byte for byte: the same label, the same challenges in the same
/// order, the same grinding schedule and the same shape refusals.
fn verify_lincheck_structured<Ch: Challenger>(
    program: &Program,
    defer: bool,
    k_log: usize,
    k_skip: usize,
    x_ab: &QuirkyPoint,
    v_a: F128,
    v_b: F128,
    proof: &LincheckProof,
    grinding: LincheckGrinding,
    challenger: &mut Ch,
) -> Result<(LincheckClaim, ExplicitClaim), LincheckError> {
    if k_skip > k_log {
        return Err(LincheckError::KSkipExceedsKLog { k_skip, k_log });
    }
    if program.block_bits() != 1usize << k_log {
        return Err(LincheckError::BadMatrixShape {
            which: "circuit",
            expected: 1usize << k_log,
            got_rows: 1usize << k_log,
            got_cols: program.block_bits(),
        });
    }
    let inner_rest_len = k_log - k_skip;
    let n_skip = 1usize << k_skip;
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
    let expected_nonces = grinding.nonce_count(inner_rest_len, 1, k_skip);
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
    let mut r_inner_rest = r_rounds;
    r_inner_rest.reverse();
    let r_inner_rest = r_inner_rest;
    let skip = x_ab.z_skip.weights(k_skip);
    let pair = |comb: Vec<F128>| comb.iter().zip(&proof.z_partial).fold(F128::ZERO, |acc, (&c, &z)| acc + c * z);
    let structured = program.structured_value(alpha, beta, &skip, &proof.z_partial, &x_ab.x_inner_rest, &r_inner_rest);
    let explicit = ExplicitClaim {
        alpha,
        skip,
        z: proof.z_partial.clone(),
        x: x_ab.x_inner_rest.clone(),
        r: r_inner_rest.clone(),
        value: running + structured,
    };
    if !defer && explicit.value != pair(program.comb_explicit(alpha, &explicit.skip, &explicit.x, &explicit.r)) {
        return Err(LincheckError::ConsistencyFailed {
            which: "sumcheck-final",
        });
    }
    let r_inner_skip = match &x_ab.z_skip {
        SkipPoint::Phi8(_) => match grinding.skip_bits(k_skip) {
            Some(bits) => SkipPoint::Phi8(ground(challenger, Some(bits), "inner-skip", &mut nonce)?),
            None => x_ab.z_skip.sample_fresh(challenger),
        },
        // The lifter's zerocheck always hands over a φ₈ skip point; the AG basis would need its
        // own fused nonce, which this replay does not carry.
        SkipPoint::Ag(_) => return Err(LincheckError::InvalidGrindingNonce { which: "inner-skip" }),
    };
    let lambda = r_inner_skip.weights(k_skip);
    let w = lambda.iter().zip(&proof.z_partial).fold(F128::ZERO, |acc, (&l, &z)| acc + l * z);
    return Ok((
        LincheckClaim {
            r_inner_skip,
            r_inner_rest: explicit.r.clone(),
            w,
        },
        explicit,
    ));
}

/// Replays the statement binding, zerocheck and lincheck of a chunk proof and rebuilds its two
/// witness claims, as Flock's single-table core verifier does.
///
/// Flock's entry first checks that `C₀` is a materialised identity matrix, because its c-claim
/// is a direct witness claim only in circuit form. The response block is in circuit form by
/// construction — every row defines its own column — and a materialised identity of `2^28` rows
/// would cost the verifier gigabytes, so this replay omits that check and nothing else.
fn verify_core_circuit_form<Ch: Challenger>(
    r1cs: &BlockR1cs,
    chunk: &ChunkProofRm,
    program: &Program,
    defer: bool,
    params: &PcsParams,
    challenger: &mut Ch,
) -> Result<(ZClaim, ZClaim, ExplicitClaim), FlockVerifyError> {
    bind_statement(challenger, r1cs, &chunk.commitment);
    let zc = verify_zerocheck_with_grinding(r1cs.m, &chunk.zerocheck, params.zerocheck_grinding(), challenger)
        .map_err(FlockVerifyError::Zerocheck)?;
    let x_ab = r1cs.x_ab_from_multilinear_values(SkipPoint::Phi8(zc.z), &zc.mlv_challenges);
    let (lc, explicit) = verify_lincheck_structured(
        program,
        defer,
        r1cs.k_log,
        r1cs.k_skip,
        &x_ab,
        zc.a_eval,
        zc.b_eval,
        &chunk.lincheck,
        params.lincheck_grinding(),
        challenger,
    )
    .map_err(FlockVerifyError::Lincheck)?;
    let ab = ZClaim {
        point: r1cs.ab_claim_point(lc.r_inner_skip, &lc.r_inner_rest, &x_ab.x_outer),
        value: lc.w,
    };
    let c = ZClaim {
        point: r1cs.c_claim_point(SkipPoint::Phi8(zc.z), &zc.r_rest),
        value: zc.c_eval,
    };
    return Ok((ab, c, explicit));
}

/// Verifies a row-major chunk proof against the published words of its blocks, discharging its
/// matrix claim in full.
pub fn verify_chunk(
    program: &Arc<Program>,
    publics: &[Vec<F128>],
    chunk: &ChunkProofRm,
    domain: &[u8],
) -> Result<(), ChunkRmError> {
    return verify_chunk_with(program, publics, chunk, domain, false).map(|_| ());
}

/// Verifies a row-major chunk proof against the published words of its blocks except for the
/// explicit rows' part of its matrix claim, which it returns for a matrix proof to discharge.
pub fn verify_chunk_deferred(
    program: &Arc<Program>,
    publics: &[Vec<F128>],
    chunk: &ChunkProofRm,
    domain: &[u8],
) -> Result<ExplicitClaim, ChunkRmError> {
    return verify_chunk_with(program, publics, chunk, domain, true);
}

fn verify_chunk_with(
    program: &Arc<Program>,
    publics: &[Vec<F128>],
    chunk: &ChunkProofRm,
    domain: &[u8],
    defer: bool,
) -> Result<ExplicitClaim, ChunkRmError> {
    let n_io = program.geometry().io_word_cols().len();
    if publics.is_empty() || publics.iter().any(|p| p.len() != n_io) {
        return Err(ChunkRmError::PublicLength);
    }
    let nu = row_log(publics.len());
    let k_log = program.geometry().k_log();
    let r1cs = r1cs_for(program, nu);
    let params = pcs_params(r1cs.m);
    let rows = padded_publics(publics, nu);
    #[cfg(feature = "count")]
    let before = count::Counts::now();
    let mut challenger = KeccakChallenger::new(domain);
    observe_publics(&mut challenger, &rows);
    let (ab, c, explicit) = verify_core_circuit_form(&r1cs, chunk, program.as_ref(), defer, &params, &mut challenger)
        .map_err(ChunkRmError::Core)?;
    #[cfg(feature = "count")]
    let core = count::Counts::now();
    let io = io_claim(&mut challenger, &rows, k_log, nu);
    verify_claims_ligerito(&chunk.commitment, &[ab, c, io], &chunk.opening, &params, &mut challenger)
        .map_err(|_| ChunkRmError::Opening)?;
    #[cfg(feature = "count")]
    {
        count::Counts::now().report_since(&core, "opening (published-word claim, ring switch, Ligerito)");
        core.report_since(&before, "core (statement binding, zerocheck, lincheck with its matrix fold)");
    }
    return Ok(explicit);
}
