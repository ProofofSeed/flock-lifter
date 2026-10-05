// SPDX-License-Identifier: LGPL-3.0-or-later
//! Multilinear helpers over GF(2^128) and GF(2^256), indices least significant variable first.

use flock_prover::field::{F128, F256};
use rayon::prelude::*;

const PAR: usize = 1 << 12;

/// The table of `eq(point, b)` over the hypercube.
pub fn eq_table(point: &[F256]) -> Vec<F256> {
    let mut t = vec![F256::ZERO; 1 << point.len()];
    t[0] = F256::ONE;
    for (i, &z) in point.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi) = t[..2 * half].split_at_mut(half);
        if half >= PAR {
            lo.par_iter_mut().zip(hi.par_iter_mut()).for_each(|(a, b)| {
                *b = *a * z;
                *a += *b;
            });
        } else {
            for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                *b = *a * z;
                *a += *b;
            }
        }
    }
    t
}

/// `eq(a, b)` for two points.
pub fn eq_eval(a: &[F256], b: &[F256]) -> F256 {
    a.iter().zip(b).fold(F256::ONE, |acc, (&x, &y)| acc * (F256::ONE + x + y))
}

/// The table of a shift weight over the hypercube: `Π_i (b_i ? c_i : 1)`.
pub fn shift_table(coords: &[F128]) -> Vec<F128> {
    let mut t = vec![F128::ZERO; 1 << coords.len()];
    t[0] = F128::ONE;
    for (i, &c) in coords.iter().enumerate() {
        let half = 1usize << i;
        let (lo, hi) = t[..2 * half].split_at_mut(half);
        if half >= PAR {
            lo.par_iter().zip(hi.par_iter_mut()).for_each(|(a, b)| *b = *a * c);
        } else {
            for (a, b) in lo.iter().zip(hi.iter_mut()) {
                *b = *a * c;
            }
        }
    }
    t
}

/// The multilinear extension of a shift weight at `point`: `Π_i (1 + y_i·(1 + c_i))`.
pub fn shift_eval(coords: &[F128], point: &[F256]) -> F256 {
    coords
        .iter()
        .zip(point)
        .fold(F256::ONE, |acc, (&c, &y)| acc * (F256::ONE + y * (F128::ONE + c)))
}

/// Binds the least significant variable of `v` to `r`.
pub fn fold(v: &[F256], r: F256) -> Vec<F256> {
    let f = |p: &[F256]| p[0] + r * (p[0] + p[1]);
    if v.len() >= 2 * PAR { v.par_chunks(2).map(f).collect() } else { v.chunks(2).map(f).collect() }
}

/// Binds the least significant variable of GF(2^128) values `v` to `r`.
pub fn fold_base(v: &[F128], r: F256) -> Vec<F256> {
    let f = |p: &[F128]| r * (p[0] + p[1]) + F256::new(p[0], F128::ZERO);
    if v.len() >= 2 * PAR { v.par_chunks(2).map(f).collect() } else { v.chunks(2).map(f).collect() }
}

/// The multilinear extension of `values` at `point`.
pub fn mle_eval(values: &[F256], point: &[F256]) -> F256 {
    assert_eq!(values.len(), 1 << point.len());
    let mut v = values.to_vec();
    for &r in point {
        v = fold(&v, r);
    }
    v[0]
}

/// The multilinear extension of GF(2^128) `values` at a GF(2^256) `point`.
pub fn mle_eval_base(values: &[F128], point: &[F256]) -> F256 {
    assert_eq!(values.len(), 1 << point.len());
    let eq = eq_table(point);
    values.par_iter().zip(eq.par_iter()).map(|(&v, &e)| e * v).reduce(|| F256::ZERO, |a, b| a + b)
}

/// The bytes of a GF(2^128) slice.
pub fn bytes_f128(v: &[F128]) -> &[u8] {
    // SAFETY: `F128` is `repr(C)` over two `u64`s with no padding.
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
}

/// The bytes of a GF(2^256) slice.
pub fn bytes_f256(v: &[F256]) -> &[u8] {
    // SAFETY: `F256` is `repr(C)` over two `F128`s with no padding.
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, std::mem::size_of_val(v)) }
}
