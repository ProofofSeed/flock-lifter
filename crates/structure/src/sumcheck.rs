// SPDX-License-Identifier: LGPL-3.0-or-later

//! Sumchecks of products of multilinear columns: round messages as coefficients, and a prover that
//! evaluates a term over the columns of every pair of rows.

use flock_prover::{
    challenger::{Challenger, grinding_bits_for_degree},
    field::F128,
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// Pairs of rows one thread takes at a time.
const CHUNK: usize = 1 << 10;

/// A sumcheck's messages: per round, every coefficient of the round polynomial but the linear one,
/// which the running claim determines, and the round's proof-of-work nonce.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rounds {
    /// Per round, the coefficients of degrees `0, 2, 3, …`.
    pub messages: Vec<Vec<F128>>,
    /// Per round, the nonce ground before its challenge.
    pub nonces: Vec<u64>,
}

/// The points round polynomials of degree `degree` are evaluated at by the prover.
pub(crate) fn nodes(degree: usize) -> Vec<F128> {
    return (0..=degree as u64).map(|i| F128::new(i, 0)).collect();
}

/// The coefficients of the polynomial of degree below `nodes.len()` taking `values` at `nodes`.
pub(crate) fn interpolate(nodes: &[F128], values: &[F128]) -> Vec<F128> {
    let n = nodes.len();
    // Newton's divided differences, then expansion.
    let mut dd = values.to_vec();
    for level in 1..n {
        for i in (level..n).rev() {
            dd[i] = (dd[i] + dd[i - 1]) * (nodes[i] + nodes[i - level]).inv();
        }
    }
    let mut coeffs = vec![F128::ZERO; n];
    for i in (0..n).rev() {
        // coeffs ← coeffs·(X + nodes[i]) + dd[i]
        for j in (1..n).rev() {
            coeffs[j] = coeffs[j - 1] + coeffs[j] * nodes[i];
        }
        coeffs[0] = coeffs[0] * nodes[i] + dd[i];
    }
    return coeffs;
}

/// The value at `r` of the round polynomial whose message is `message` under running claim `claim`.
pub(crate) fn evaluate(claim: F128, message: &[F128], r: F128) -> F128 {
    // g(0) + g(1) = claim, so the coefficients of degree one and above sum to the claim.
    let linear = message[1..].iter().fold(claim, |acc, &c| acc + c);
    let mut acc = F128::ZERO;
    for &c in message[1..].iter().rev() {
        acc = acc * r + c;
    }
    return (acc * r + linear) * r + message[0];
}

/// A term of a sumcheck: a polynomial in the values of the columns at one row.
pub trait Term: Sync {
    /// The term's degree in any one variable.
    fn degree(&self) -> usize;
    /// The term at one row's column values.
    fn eval(&self, row: &[F128]) -> F128;
}

/// Proves `Σ_rows term(columns at the row) = claim`, binding the low variable first; returns the
/// rounds, the point and the columns' extensions there.
pub fn prove<T: Term, Ch: Challenger>(
    term: &T,
    mut columns: Vec<Vec<F128>>,
    mut claim: F128,
    ch: &mut Ch,
) -> (Rounds, Vec<F128>, Vec<F128>) {
    let degree = term.degree();
    let nodes = nodes(degree);
    let bits = grinding_bits_for_degree(degree);
    let width = columns.len();
    let vars = columns[0].len().trailing_zeros() as usize;
    assert!(columns.iter().all(|c| c.len() == 1 << vars));
    let mut rounds = Rounds {
        messages: Vec::with_capacity(vars),
        nonces: Vec::with_capacity(vars),
    };
    let mut point = Vec::with_capacity(vars);
    for _ in 0..vars {
        let pairs = columns[0].len() / 2;
        let values = (0..pairs.div_ceil(CHUNK))
            .into_par_iter()
            .map(|c| {
                let mut acc = vec![F128::ZERO; degree + 1];
                let (mut lo, mut delta, mut row) = (vec![F128::ZERO; width], vec![F128::ZERO; width], vec![F128::ZERO; width]);
                for p in c * CHUNK..((c + 1) * CHUNK).min(pairs) {
                    for (w, column) in columns.iter().enumerate() {
                        lo[w] = column[2 * p];
                        delta[w] = column[2 * p] + column[2 * p + 1];
                    }
                    acc[0] += term.eval(&lo);
                    for (j, &x) in nodes.iter().enumerate().skip(1) {
                        for w in 0..width {
                            row[w] = if delta[w] == F128::ZERO { lo[w] } else { lo[w] + x * delta[w] };
                        }
                        acc[j] += term.eval(&row);
                    }
                }
                acc
            })
            .reduce(
                || vec![F128::ZERO; degree + 1],
                |mut a, b| {
                    a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
                    a
                },
            );
        debug_assert_eq!(values[0] + values[1], claim, "the round polynomial sums to the running claim");
        let coeffs = interpolate(&nodes, &values);
        let message: Vec<F128> = coeffs.iter().enumerate().filter(|&(i, _)| i != 1).map(|(_, &c)| c).collect();
        ch.observe_f128_slice(&message);
        let (nonce, r) = ch.grind_pow_and_sample_f128(bits);
        claim = evaluate(claim, &message, r);
        rounds.messages.push(message);
        rounds.nonces.push(nonce);
        point.push(r);
        columns.par_iter_mut().for_each(|column| {
            for p in 0..pairs {
                let (a, b) = (column[2 * p], column[2 * p + 1]);
                column[p] = if a == b { a } else { a + r * (a + b) };
            }
            column.truncate(pairs);
        });
    }
    let finals = columns.iter().map(|c| c[0]).collect();
    return (rounds, point, finals);
}

/// Replays a sumcheck of `vars` rounds of degree `degree` from `claim`; returns the final claim and
/// the point.
pub fn verify<Ch: Challenger>(degree: usize, vars: usize, mut claim: F128, rounds: &Rounds, ch: &mut Ch) -> Option<(F128, Vec<F128>)> {
    if rounds.messages.len() != vars || rounds.nonces.len() != vars || rounds.messages.iter().any(|m| m.len() != degree) {
        return None;
    }
    let bits = grinding_bits_for_degree(degree);
    let mut point = Vec::with_capacity(vars);
    for (message, &nonce) in rounds.messages.iter().zip(&rounds.nonces) {
        ch.observe_f128_slice(message);
        let r = ch.verify_pow_and_sample_f128(nonce, bits)?;
        claim = evaluate(claim, message, r);
        point.push(r);
    }
    return Some((claim, point));
}

/// `Π_i (1 + p_i + v_i)`: the extension of the indicator of `p` at the bit values `v`.
#[inline]
pub fn eq(point: &[F128], bits: &[F128]) -> F128 {
    return point.iter().zip(bits).fold(F128::ONE, |acc, (&p, &v)| acc * (F128::ONE + p + v));
}
