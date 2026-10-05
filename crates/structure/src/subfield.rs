// SPDX-License-Identifier: LGPL-3.0-or-later

//! Bytes as elements of the subfield `GF(2^8)` of `GF(2^128)`, and the evaluation of their bits'
//! multilinear extensions from the bytes' own at Frobenius conjugates of the point.
//!
//! A byte `v` is committed as `φ(v)`, the image of `v` under Flock's embedding of the AES field.
//! Bit `i` of `v` is the trace `Tr(δ_i·φ(v))` to `GF(2)` for the basis `δ` dual to `φ(1), φ(2), …,
//! φ(128)`, and a trace is a sum of Frobenius powers, which a multilinear extension over `GF(2)`
//! commutes with: for a table `P` of bytes and its bit `i`'s table `B_i`,
//!
//! `B̃_i(θ) = Σ_{j<8} δ_i^(2^j) · P̃(θ^(2^-j))^(2^j)`.

use std::sync::OnceLock;

use flock_prover::field::{F128, PHI_8_TABLE};

/// Bits of a byte, and Frobenius conjugates of a point.
pub const DEGREE: usize = 8;

/// The committed form of a byte.
#[inline]
pub fn embed(byte: u8) -> F128 {
    return PHI_8_TABLE[byte as usize];
}

/// `x^(2^j)`.
pub fn frobenius(x: F128, j: usize) -> F128 {
    let mut y = x;
    for _ in 0..j {
        y = y * y;
    }
    return y;
}

/// The square root `x^(2^127)`.
pub fn sqrt(x: F128) -> F128 {
    return frobenius(x, 127);
}

/// `δ_i^(2^j)` at `[i][j]`, for the basis `δ` of the subfield dual to the bits' under the trace.
pub fn dual() -> &'static [[F128; DEGREE]; DEGREE] {
    static DUAL: OnceLock<[[F128; DEGREE]; DEGREE]> = OnceLock::new();
    return DUAL.get_or_init(|| {
        let trace = |u: F128| -> bool {
            let t = (0..DEGREE).fold(F128::ZERO, |acc, j| acc + frobenius(u, j));
            assert!(t == F128::ZERO || t == F128::ONE, "a trace lies in GF(2)");
            t == F128::ONE
        };
        let mut out = [[F128::ZERO; DEGREE]; DEGREE];
        for (i, row) in out.iter_mut().enumerate() {
            let delta = (1..=255u8)
                .map(embed)
                .find(|&d| (0..DEGREE).all(|k| trace(d * embed(1 << k)) == (i == k)))
                .expect("the trace form is non-degenerate");
            for (j, slot) in row.iter_mut().enumerate() {
                *slot = frobenius(delta, j);
            }
        }
        out
    });
}

/// The conjugates `θ, θ^(1/2), …, θ^(1/128)` of a point, coordinate by coordinate.
pub fn conjugates(point: &[F128]) -> Vec<Vec<F128>> {
    let mut out = vec![point.to_vec()];
    for j in 1..DEGREE {
        out.push(out[j - 1].iter().map(|&x| sqrt(x)).collect());
    }
    return out;
}

/// Whether `points` are the conjugates of their first.
pub fn are_conjugates(points: &[Vec<F128>]) -> bool {
    return points.len() == DEGREE && points.windows(2).all(|w| w[0].len() == w[1].len() && w[1].iter().zip(&w[0]).all(|(&r, &x)| r * r == x));
}

/// The bits' extensions at a point from the bytes' extension at its conjugates.
pub fn bits(at_conjugates: &[F128]) -> [F128; DEGREE] {
    assert_eq!(at_conjugates.len(), DEGREE);
    let dual = dual();
    let powers: Vec<F128> = at_conjugates.iter().enumerate().map(|(j, &y)| frobenius(y, j)).collect();
    return std::array::from_fn(|i| powers.iter().zip(&dual[i]).fold(F128::ZERO, |acc, (&p, &d)| acc + d * p));
}

/// The extension of a table of bits packed in bytes at a point whose three low coordinates address
/// the bit, from the bytes' extension at the conjugates of the rest of the point.
pub fn bit_value(low: &[F128], at_conjugates: &[F128]) -> F128 {
    assert_eq!(low.len(), 3);
    let b = bits(at_conjugates);
    let mut eq = [F128::ONE; DEGREE];
    for (v, &x) in low.iter().enumerate() {
        for (i, e) in eq.iter_mut().enumerate() {
            *e *= if i >> v & 1 == 1 { x } else { F128::ONE + x };
        }
    }
    return b.iter().zip(&eq).fold(F128::ZERO, |acc, (&b, &e)| acc + b * e);
}
