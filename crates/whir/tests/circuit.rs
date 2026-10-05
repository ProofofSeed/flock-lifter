// SPDX-License-Identifier: LGPL-3.0-or-later
//! Flock's in-circuit WHIR verifier accepts honest recorded openings across configurations.

use flock_prover::challenger::FsChallenger;
use flock_prover::field::{F128, F256};
use flock_prover::tower::build_whir_circuit;
use flock_prover::transcript_record::RecordingChallenger;
use pofseed_flock_lift_whir::params::{Config, Regime};
use pofseed_flock_lift_whir::record::whir_record;
use pofseed_flock_lift_whir::whir;

fn sample(n: usize, seed: u64) -> Vec<F128> {
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

#[test]
fn recorded_openings_verify_in_circuit() {
    for (num_vars, folding, rate, regime, pow_bits) in [
        (12, 4, 1, Regime::Johnson, 8),
        (14, 4, 2, Regime::Johnson, 4),
        (13, 3, 1, Regime::UniqueDecoding, 0),
    ] {
        let config = Config {
            num_vars,
            folding,
            log_inv_rate: rate,
            security_bits: 100,
            pow_bits,
            final_vars: 4,
            regime,
        };
        let message = sample(1 << num_vars, 5);
        let point: Vec<F256> =
            sample(2 * num_vars, 9).chunks(2).map(|c| F256::new(c[0], c[1])).collect();
        let domain = b"whir-circuit-test";
        let (c, committed) = whir::commit(&config, message).unwrap();
        let (values, proof) = whir::open(
            committed,
            std::slice::from_ref(&point),
            &mut FsChallenger::with_chained_blake3(domain),
        );
        let mut rec = RecordingChallenger::new(FsChallenger::with_chained_blake3(domain));
        whir::verify(&config, &c, std::slice::from_ref(&point), &values, &proof, &mut rec)
            .expect("verifies");
        let record = whir_record(&config, &c, &proof, 1);
        let (b3_rows, need) = build_whir_circuit(&rec, domain, &record);
        eprintln!(
            "m {num_vars} k {folding} rate {rate} {regime:?}: {b3_rows} BLAKE3 rows, {need} rows in the fullest slot"
        );
    }
}

#[test]
#[should_panic(expected = "disagrees")]
fn a_tampered_merkle_sibling_fails_the_circuit() {
    let config = Config {
        num_vars: 12,
        folding: 4,
        log_inv_rate: 1,
        security_bits: 100,
        pow_bits: 8,
        final_vars: 4,
        regime: Regime::Johnson,
    };
    let message = sample(1 << 12, 5);
    let point: Vec<F256> = sample(24, 9).chunks(2).map(|c| F256::new(c[0], c[1])).collect();
    let domain = b"whir-circuit-test";
    let (c, committed) = whir::commit(&config, message).unwrap();
    let (values, proof) = whir::open(
        committed,
        std::slice::from_ref(&point),
        &mut FsChallenger::with_chained_blake3(domain),
    );
    let mut rec = RecordingChallenger::new(FsChallenger::with_chained_blake3(domain));
    whir::verify(&config, &c, std::slice::from_ref(&point), &values, &proof, &mut rec).unwrap();
    let mut record = whir_record(&config, &c, &proof, 1);
    record.functions[1].paths[3][0][0] ^= 1;
    build_whir_circuit(&rec, domain, &record);
}
