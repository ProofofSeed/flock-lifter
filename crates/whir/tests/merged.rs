// SPDX-License-Identifier: LGPL-3.0-or-later
//! Flock's merged opening over a full-height stack opens bit-level claims on row-major words.

use flock_prover::challenger::{Challenger, FsChallenger};
use flock_prover::field::F128;
use flock_prover::lincheck::{SkipPoint, build_eq_table};
use flock_prover::merkle::HashKind;
use flock_prover::pcs::ligerito::{LigeritoProfile, embedded_initial_k_or_default};
use flock_prover::pcs::{self, PcsParams, open_batch_merged, verify_batch_merged};
use flock_prover::zerocheck::PaddingSpec;

fn random(n: usize, seed: u64) -> Vec<F128> {
    let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            F128::new(x, x.rotate_left(29))
        })
        .collect()
}

fn claim_value(words: &[F128], skip: &[F128], r6: F128, rest: &[F128]) -> F128 {
    let eq = build_eq_table(rest);
    words.iter().zip(&eq).fold(F128::ZERO, |acc, (w, &e)| {
        let mut v = F128::ZERO;
        for b in 0..128 {
            let bit = if b < 64 { (w.lo >> b) & 1 } else { (w.hi >> (b - 64)) & 1 };
            if bit == 1 {
                v += skip[b & 63] * if b < 64 { F128::ONE + r6 } else { r6 };
            }
        }
        acc + e * v
    })
}

#[test]
fn a_full_height_stack_opens_through_the_merged_transport() {
    let m = 22;
    let words_log = m - 7;
    let profile = LigeritoProfile::Fast;
    let params = PcsParams {
        m,
        log_inv_rate: profile.log_inv_rate(),
        log_batch_size: embedded_initial_k_or_default(m, profile),
        profile,
        num_lanes: None,
        merkle_hash: HashKind::Blake3,
    };
    let words = random(1 << words_log, 7);
    let claims: Vec<(SkipPoint, Vec<F128>, F128)> = (0..2)
        .map(|i| {
            let point = random(words_log + 2, 99 + i);
            let skip = SkipPoint::Phi8(point[0]);
            let value = claim_value(&words, &skip.weights(6), point[1], &point[2..]);
            (skip, point[1..].to_vec(), value)
        })
        .collect();
    for n_log in [3, words_log / 2, words_log] {
        let heights = vec![1u64 << n_log; 1 << (words_log - n_log)];
        let (commitment, prover_data) = pcs::commit(&words, &params);
        let lig = params.ligerito_prover_config().unwrap();
        let x_refs: Vec<&[F128]> = claims.iter().map(|c| c.1.as_slice()).collect();
        let mut ch = FsChallenger::with_chained_blake3(b"merged-test");
        ch.observe_bytes(commitment.cap.as_flattened());
        let proof = open_batch_merged(
            words.clone(),
            None,
            &prover_data,
            &commitment,
            &x_refs,
            &[None, None],
            &[None, None],
            &[],
            &PaddingSpec::dense(m),
            &heights,
            n_log,
            &lig,
            params.opening_grinding(),
            None,
            &mut ch,
        );
        let verify = |values: &[F128]| {
            let mut ch = FsChallenger::with_chained_blake3(b"merged-test");
            ch.observe_bytes(commitment.cap.as_flattened());
            verify_batch_merged(
                &commitment,
                values,
                &claims.iter().map(|c| c.0).collect::<Vec<_>>(),
                &x_refs,
                &[],
                &heights,
                n_log,
                &proof,
                &params.ligerito_verifier_config().unwrap(),
                params.opening_grinding(),
                None,
                &mut ch,
            )
        };
        let values: Vec<F128> = claims.iter().map(|c| c.2).collect();
        verify(&values).unwrap_or_else(|e| panic!("n_log {n_log}: {e:?}"));
        let mut wrong = values.clone();
        wrong[1] += F128::ONE;
        assert!(verify(&wrong).is_err(), "n_log {n_log}: a wrong value");
    }
}
