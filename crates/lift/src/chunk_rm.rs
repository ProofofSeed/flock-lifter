// SPDX-License-Identifier: LGPL-3.0-or-later

//! A Flock proof over a batch of response blocks through the single-table row-major path, with
//! the published words bound by one extra evaluation claim on the committed witness.

use std::sync::{Arc, OnceLock};

use flock_prover::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    lincheck::{
        LincheckCircuit, QuirkyPoint, SkipPoint, pack_z_lincheck_from_packed,
        verify_with_grinding as verify_lincheck_with_grinding,
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

/// The Ligerito profile every chunk is proved under: `Fast` (rate 1/2) unless
/// `POFSEED_LIGERITO_PROFILE` selects `slim` (rate 1/4, about half the proof for about twice the
/// encoding work) or `secure` (the unique-decoding regime).
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

fn pcs_params(m: usize) -> PcsParams {
    let profile = profile();
    return PcsParams {
        m,
        log_inv_rate: profile.log_inv_rate(),
        log_batch_size: embedded_initial_k_or_default(m, profile),
        profile,
        num_lanes: None,
        merkle_hash: Default::default(),
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
    let mut challenger = FsChallenger::new(domain);
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
    circuit: &dyn LincheckCircuit,
    params: &PcsParams,
    challenger: &mut Ch,
) -> Result<(ZClaim, ZClaim), FlockVerifyError> {
    bind_statement(challenger, r1cs, &chunk.commitment);
    let zc = verify_zerocheck_with_grinding(r1cs.m, &chunk.zerocheck, params.zerocheck_grinding(), challenger)
        .map_err(FlockVerifyError::Zerocheck)?;
    let x_ab = r1cs.x_ab_from_multilinear_values(SkipPoint::Phi8(zc.z), &zc.mlv_challenges);
    let lc = verify_lincheck_with_grinding(
        r1cs.m,
        r1cs.k_log,
        r1cs.k_skip,
        circuit,
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
    return Ok((ab, c));
}

/// Verifies a row-major chunk proof against the published words of its blocks.
pub fn verify_chunk(
    program: &Arc<Program>,
    publics: &[Vec<F128>],
    chunk: &ChunkProofRm,
    domain: &[u8],
) -> Result<(), ChunkRmError> {
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
    let mut challenger = FsChallenger::new(domain);
    observe_publics(&mut challenger, &rows);
    let (ab, c) = verify_core_circuit_form(&r1cs, chunk, program.as_ref(), &params, &mut challenger)
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
    return Ok(());
}
