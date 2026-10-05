// SPDX-License-Identifier: LGPL-3.0-or-later

//! The reduction of several claims on the committed bytes' bits to one.
//!
//! For claims `B̃(p_k) = v_k` on the extension `B̃` of the bits and a challenge `λ`, a sumcheck of
//! `Σ_b W(b)·B(b) = Σ_k λ^k·v_k` with `W = Σ_k λ^k·eq(p_k, ·)` leaves one claim `B̃(r)·W̃(r)`, in
//! which the verifier computes `W̃(r)` itself. The variables are bound lowest first: the three of
//! a bit's index in its byte, then the bytes'.
//!
//! The prover never holds a table over the bits. While it binds a bit's index, a claim's share of
//! a round polynomial depends on a byte through its value alone, so the claim's weights are summed
//! per value once. After that the bits' table is a function of the byte, and both tables are held
//! over the bytes.

use flock_prover::{challenger::{Challenger, grinding_bits_for_degree}, field::F128, lincheck::build_eq_table};
use rayon::prelude::*;

use crate::sumcheck::{self, Rounds, Term, eq, evaluate, interpolate, nodes};

/// Variables of a bit's index in its byte.
const BIT_VARS: usize = 3;

/// The product of two columns.
struct Pair;

impl Term for Pair {
    fn degree(&self) -> usize {
        return 2;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        return row[0] * row[1];
    }
}

/// `Σ_k λ^k·v_k` over the claims' values.
pub fn target(claims: &[(Vec<F128>, F128)], lambda: F128) -> F128 {
    return claims.iter().rev().fold(F128::ZERO, |acc, (_, v)| acc * lambda + *v);
}

/// `Σ_k λ^k·eq(p_k, r)` over the claims' points.
pub fn weight(claims: &[(Vec<F128>, F128)], lambda: F128, r: &[F128]) -> F128 {
    return claims.iter().rev().fold(F128::ZERO, |acc, (p, _)| acc * lambda + eq(p, r));
}

/// The extension of the bits of `byte` at a point over a bit's index.
fn bit_extension(byte: usize, q: &[F128; BIT_VARS]) -> F128 {
    return (0..1usize << BIT_VARS).filter(|i| byte >> i & 1 == 1).fold(F128::ZERO, |acc, i| {
        acc + (0..BIT_VARS).fold(F128::ONE, |e, j| e * if i >> j & 1 == 1 { q[j] } else { F128::ONE + q[j] })
    });
}

/// A claim's weights over the bytes: the block they are supported on and the weights there.
struct Support {
    offset: usize,
    weights: Vec<F128>,
}

impl Support {
    /// The weights `eq(point, ·)` of a point over the bytes, whose trailing coordinates in `{0, 1}`
    /// select a block.
    fn new(point: &[F128]) -> Self {
        let boolean = |x: &F128| *x == F128::ZERO || *x == F128::ONE;
        let log = point.len() - point.iter().rev().take_while(|x| boolean(x)).count();
        let offset = point[log..].iter().enumerate().fold(0usize, |acc, (i, &x)| acc | usize::from(x == F128::ONE) << (log + i));
        return Self { offset, weights: build_eq_table(&point[..log]) };
    }

    /// The weights' sums over the bytes of each value.
    fn by_value(&self, bytes: &[u8]) -> Vec<F128> {
        let block = &bytes[self.offset..self.offset + self.weights.len()];
        return block
            .par_chunks(1 << 16)
            .zip(self.weights.par_chunks(1 << 16))
            .map(|(b, w)| {
                let mut sums = vec![F128::ZERO; 256];
                b.iter().zip(w).for_each(|(&v, &e)| sums[v as usize] += e);
                sums
            })
            .reduce(
                || vec![F128::ZERO; 256],
                |mut a, b| {
                    a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
                    a
                },
            );
    }
}

/// Proves the reduction of `claims` on the bits of `bytes` under `lambda`; returns the rounds and
/// the point.
pub fn prove<Ch: Challenger>(bytes: &[u8], claims: &[(Vec<F128>, F128)], lambda: F128, ch: &mut Ch) -> (Rounds, Vec<F128>) {
    assert!(bytes.len().is_power_of_two());
    let n = bytes.len().trailing_zeros() as usize;
    assert!(claims.iter().all(|(p, _)| p.len() == BIT_VARS + n));
    let supports: Vec<Support> = claims.iter().map(|(p, _)| Support::new(&p[BIT_VARS..])).collect();
    let sums: Vec<Vec<F128>> = supports.iter().map(|s| s.by_value(bytes)).collect();
    let powers: Vec<F128> = std::iter::successors(Some(F128::ONE), |&p| Some(p * lambda)).take(claims.len()).collect();
    let mut claim = target(claims, lambda);
    let nodes = nodes(2);
    let bits = grinding_bits_for_degree(2);
    let mut rounds = Rounds { messages: Vec::new(), nonces: Vec::new() };
    let mut low: Vec<F128> = Vec::with_capacity(BIT_VARS);
    for t in 0..BIT_VARS {
        let values: Vec<F128> = nodes
            .iter()
            .map(|&x| {
                let mut total = F128::ZERO;
                for rest in 0..1usize << (BIT_VARS - 1 - t) {
                    let q: [F128; BIT_VARS] = std::array::from_fn(|j| match j.cmp(&t) {
                        std::cmp::Ordering::Less => low[j],
                        std::cmp::Ordering::Equal => x,
                        std::cmp::Ordering::Greater => if rest >> (j - t - 1) & 1 == 1 { F128::ONE } else { F128::ZERO },
                    });
                    let table: Vec<F128> = (0..256).map(|v| bit_extension(v, &q)).collect();
                    for ((point, _), (sum, &power)) in claims.iter().zip(sums.iter().zip(&powers)) {
                        let inner = sum.iter().zip(&table).fold(F128::ZERO, |acc, (&s, &b)| acc + s * b);
                        total += power * eq(&point[..BIT_VARS], &q) * inner;
                    }
                }
                total
            })
            .collect();
        debug_assert_eq!(values[0] + values[1], claim, "the round polynomial sums to the running claim");
        let coeffs = interpolate(&nodes, &values);
        let message = vec![coeffs[0], coeffs[2]];
        ch.observe_f128_slice(&message);
        let (nonce, r) = ch.grind_pow_and_sample_f128(bits);
        claim = evaluate(claim, &message, r);
        rounds.messages.push(message);
        rounds.nonces.push(nonce);
        low.push(r);
    }
    let q: [F128; BIT_VARS] = [low[0], low[1], low[2]];
    let table: Vec<F128> = (0..256).map(|v| bit_extension(v, &q)).collect();
    let mut weights = vec![F128::ZERO; bytes.len()];
    for (((point, _), support), &power) in claims.iter().zip(supports).zip(&powers) {
        let scale = power * eq(&point[..BIT_VARS], &q);
        let block = &mut weights[support.offset..support.offset + support.weights.len()];
        block.par_iter_mut().zip(support.weights.par_iter()).for_each(|(w, &e)| *w += scale * e);
    }
    let values: Vec<F128> = bytes.par_iter().map(|&v| table[v as usize]).collect();
    let (rest, high, _) = sumcheck::prove(&Pair, vec![weights, values], claim, ch);
    rounds.messages.extend(rest.messages);
    rounds.nonces.extend(rest.nonces);
    low.extend(high);
    return (rounds, low);
}
