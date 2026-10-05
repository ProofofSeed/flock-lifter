// SPDX-License-Identifier: LGPL-3.0-or-later

//! The multilinear extension of a cyclic shift: `(t, u) ↦ eq(b, (t + u) mod 2^n)`.

use flock_prover::field::F128;

/// `Σ_{t,u < 2^n} eq(x, t)·eq(y, u)·eq(b, (t + u) mod 2^n)` for points of `n` coordinates each,
/// least significant first.
pub fn rotated_eq(x: &[F128], y: &[F128], b: &[F128]) -> F128 {
    assert!(x.len() == y.len() && y.len() == b.len());
    // `v[c]` is the sum over the low bits handled so far that leave carry `c`.
    let mut v = [F128::ONE, F128::ZERO];
    for ((&xi, &yi), &bi) in x.iter().zip(y).zip(b) {
        let both = xi * yi;
        // Weights of `t_i + u_i` being 0, 1 and 2.
        let (w0, w1, w2) = (F128::ONE + xi + yi + both, xi + yi, both);
        // Weights of the sum bit being 0 and 1.
        let (e0, e1) = (F128::ONE + bi, bi);
        v = [v[0] * (w0 * e0 + w1 * e1) + v[1] * (w0 * e1), v[0] * (w2 * e0) + v[1] * (w1 * e0 + w2 * e1)];
    }
    return v[0] + v[1];
}
