// SPDX-License-Identifier: LGPL-3.0-or-later
//! Honest openings verify across configurations, and every part of a proof refuses tampering.

use flock_prover::challenger::FsChallenger;
use flock_prover::field::{F128, F256};
use pofseed_flock_lift_whir::field::{mle_eval, mle_eval_base};
use pofseed_flock_lift_whir::params::{Config, MerkleHash, Regime};
use pofseed_flock_lift_whir::whir::{self, Commitment, Openings, Proof, VerifyError, Weight};

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

fn point(vars: usize, seed: u64) -> Vec<F256> {
    let v = sample(2 * vars, seed);
    v.chunks(2).map(|c| F256::new(c[0], c[1])).collect()
}

fn config(num_vars: usize, folding: usize, log_inv_rate: usize, regime: Regime) -> Config {
    Config {
        num_vars,
        folding,
        log_inv_rate,
        security_bits: 100,
        pow_bits: 8,
        final_vars: 4,
        regime,
        merkle: Default::default(),
    }
}

fn prove(
    config: &Config,
    seed: u64,
    claims: usize,
) -> (Commitment, Vec<Vec<F256>>, Vec<F256>, Proof) {
    let message = sample(1 << config.num_vars, seed);
    let points: Vec<Vec<F256>> =
        (0..claims).map(|i| point(config.num_vars, seed + 100 + i as u64)).collect();
    let mut ch = FsChallenger::new(b"whir-test");
    let (commitment, committed) = whir::commit(config, message.clone()).unwrap();
    let (values, proof) = whir::open(committed, &points, &mut ch);
    for (z, v) in points.iter().zip(&values) {
        assert_eq!(*v, mle_eval_base(&message, z), "the opened value is the polynomial's");
    }
    (commitment, points, values, proof)
}

fn check(
    config: &Config,
    c: &Commitment,
    p: &[Vec<F256>],
    v: &[F256],
    proof: &Proof,
) -> Result<(), VerifyError> {
    whir::verify(config, c, p, v, proof, &mut FsChallenger::new(b"whir-test"))
}

#[test]
fn honest_openings_verify() {
    for (vars, folding, rate, regime, claims) in [
        (10, 2, 1, Regime::UniqueDecoding, 1),
        (12, 4, 1, Regime::Johnson, 1),
        (13, 3, 2, Regime::Johnson, 2),
        (14, 4, 2, Regime::UniqueDecoding, 3),
        (9, 5, 1, Regime::Johnson, 1),
        (16, 4, 1, Regime::Johnson, 1),
    ] {
        let config = config(vars, folding, rate, regime);
        let schedule = config.schedule().unwrap();
        let (c, p, v, proof) = prove(&config, vars as u64, claims);
        eprintln!(
            "m={vars} k={folding} 1/ρ=2^{rate} {regime:?}: rounds {:?}, queries {:?}, proof {} B",
            schedule.rounds.len(),
            schedule.rounds.iter().map(|r| r.queries).collect::<Vec<_>>(),
            proof.to_bytes().len()
        );
        check(&config, &c, &p, &v, &proof).expect("an honest opening verifies");
    }
}

#[test]
fn tampering_is_refused() {
    let config = config(12, 4, 1, Regime::Johnson);
    let (c, p, v, proof) = prove(&config, 7, 1);
    check(&config, &c, &p, &v, &proof).unwrap();
    let mut value = v.clone();
    value[0] += F256::ONE;
    assert!(check(&config, &c, &p, &value, &proof).is_err(), "another value");
    let mut other = p.clone();
    other[0][3] += F256::ONE;
    assert!(check(&config, &c, &other, &v, &proof).is_err(), "another point");
    let mut t = proof.clone();
    t.sumcheck[2][0] += F256::ONE;
    assert!(check(&config, &c, &p, &v, &t).is_err(), "a sumcheck message");
    let mut t = proof.clone();
    t.final_poly[1] += F256::ONE;
    assert!(check(&config, &c, &p, &v, &t).is_err(), "the final polynomial");
    let mut t = proof.clone();
    t.rounds[0].ood[0] += F256::ONE;
    assert!(check(&config, &c, &p, &v, &t).is_err(), "an out-of-domain answer");
    let mut t = proof.clone();
    t.rounds[0].pow ^= 1;
    assert!(matches!(check(&config, &c, &p, &v, &t), Err(VerifyError::Pow(_)) | Err(_)), "a nonce");
    let mut t = proof.clone();
    if let Openings::Base(rows, _) = &mut t.rounds[0].openings {
        rows[5] += F128::ONE;
    }
    assert!(matches!(check(&config, &c, &p, &v, &t), Err(VerifyError::Merkle(0))), "an opened row");
    let mut t = proof.clone();
    if let Openings::Ext(rows, _) = &mut t.final_openings {
        rows[0] += F256::ONE;
    }
    assert!(check(&config, &c, &p, &v, &t).is_err(), "a final opened row");
    let mut commitment = c.clone();
    commitment.cap[0][0] ^= 1;
    assert!(check(&config, &commitment, &p, &v, &proof).is_err(), "another commitment");
    let mut t = proof.clone();
    t.ood[0] += F256::ONE;
    assert!(check(&config, &c, &p, &v, &t).is_err(), "another initial out-of-domain answer");
}

#[test]
fn a_different_polynomial_does_not_open_to_the_same_value() {
    let config = config(12, 4, 1, Regime::Johnson);
    let (c, p, v, _) = prove(&config, 11, 1);
    let (_, _, _, other) = prove(&config, 12, 1);
    assert!(check(&config, &c, &p, &v, &other).is_err(), "another polynomial's proof");
}

struct Dense(Vec<F256>);

impl Weight for Dense {
    fn table(&self) -> Vec<F256> {
        self.0.clone()
    }

    fn eval(&self, point: &[F256]) -> F256 {
        mle_eval(&self.0, point)
    }
}

#[test]
fn weighted_openings_verify_and_bind_their_sums() {
    for (vars, folding, rate, regime) in [
        (10, 2, 1, Regime::UniqueDecoding),
        (12, 4, 1, Regime::Johnson),
        (13, 3, 2, Regime::Johnson),
    ] {
        let config = config(vars, folding, rate, regime);
        let message = sample(1 << vars, 3);
        let weights: Vec<Dense> = (0..2).map(|i| Dense(point(1 << vars, 40 + i))).collect();
        let dyn_weights: Vec<&dyn Weight> = weights.iter().map(|w| w as &dyn Weight).collect();
        let points = vec![point(vars, 60)];
        let mut ch = FsChallenger::new(b"whir-test");
        let (c, committed) = whir::commit(&config, message.clone()).unwrap();
        let (values, sums, proof) = whir::open_weighted(committed, &points, &dyn_weights, &mut ch);
        for (w, s) in weights.iter().zip(&sums) {
            let expected = w.0.iter().zip(&message).fold(F256::ZERO, |a, (&x, &y)| a + x * y);
            assert_eq!(*s, expected, "the weighted sum is the polynomial's");
        }
        let check = |sums: &[F256], weights: &[&dyn Weight]| {
            whir::verify_weighted(
                &config,
                &c,
                &points,
                &values,
                weights,
                sums,
                &proof,
                &mut FsChallenger::new(b"whir-test"),
            )
        };
        check(&sums, &dyn_weights).expect("an honest weighted opening verifies");
        let mut other = sums.clone();
        other[1] += F256::ONE;
        assert!(check(&other, &dyn_weights).is_err(), "another sum");
        let mut table = weights[0].0.clone();
        table[5] += F256::ONE;
        let changed = Dense(table);
        assert!(check(&sums, &[&changed, dyn_weights[1]]).is_err(), "another weight");
    }
}

#[test]
fn keccak_trees_open_and_refuse_tampered_rows() {
    for (vars, folding, rate) in [(12, 4, 1), (13, 3, 3)] {
        let config = Config { merkle: MerkleHash::Keccak, ..config(vars, folding, rate, Regime::Johnson) };
        let (c, p, v, proof) = prove(&config, 5, 2);
        check(&config, &c, &p, &v, &proof).expect("an honest opening verifies");
        let mut t = proof.clone();
        if let Openings::Base(rows, _) = &mut t.rounds[0].openings {
            rows[3] += F128::ONE;
        }
        assert!(matches!(check(&config, &c, &p, &v, &t), Err(VerifyError::Merkle(0))), "an opened row");
        let mut t = proof.clone();
        if let Openings::Ext(_, paths) = &mut t.final_openings {
            paths[0][0][7] ^= 1;
        }
        assert!(check(&config, &c, &p, &v, &t).is_err(), "a path");
        let blake = Config { merkle: MerkleHash::Blake3, ..config };
        assert!(check(&blake, &c, &p, &v, &proof).is_err(), "another hash");
    }
}
