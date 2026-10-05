// SPDX-License-Identifier: LGPL-3.0-or-later

//! The opening of a wrap's outer proof, as the contract computes it: Flock's merged transport of
//! the claims onto one evaluation of the committed stack, with the linearised coefficients, the
//! twisted equality and the layout's weights in closed form.

use std::sync::OnceLock;

use flock_prover::{
    challenger::Challenger,
    field::F128,
    lincheck::build_eq_table,
    pcs::jagged::{STATE_INITIAL, STATE_SUCCESS, assist_sparse_transitions},
    zerocheck::multilinear::lagrange_weights_naive,
};
use pofseed_flock_lift::transcript::KeccakChallenger;

use crate::{
    mirror::{Reader, Reject, Result, dot, pow_f128, pow_vec, read_n},
    wrap::{
        outer::{Piops, quadratic},
        trace,
        vk::Vk,
    },
};

/// Bits of a committed word.
const WORD: usize = 128;

/// The field's generator `x` under Frobenius, `x^(2^k)` at `[k]`, and the same powers of the
/// inverse of the modulus's derivative at `x`, `(x^6 + 1)^-1`.
pub fn frobenius_constants() -> &'static ([F128; WORD], [F128; WORD]) {
    static T: OnceLock<([F128; WORD], [F128; WORD])> = OnceLock::new();
    return T.get_or_init(|| {
        let x = F128::new(2, 0);
        let mut x6 = F128::ONE;
        for _ in 0..6 {
            x6 *= x;
        }
        let (mut beta, mut d) = ([F128::ZERO; WORD], [F128::ZERO; WORD]);
        (beta[0], d[0]) = (x, (x6 + F128::ONE).inv());
        for k in 1..WORD {
            beta[k] = beta[k - 1] * beta[k - 1];
            d[k] = d[k - 1] * d[k - 1];
        }
        (beta, d)
    });
}

/// The coefficients `c_j` with `Σ_t bit_t(v)·gamma·eq(r, t) = Σ_j c_j·v^(2^j)` for every word `v`,
/// from the trace-dual of the polynomial basis: `c_j = d^(2^j)·Σ_t e_t·b_t(x^(2^j))` with
/// `b_t(X) = Σ_{i>t} f_i·X^(i−t−1)` over the modulus `f = X^128 + X^7 + X^2 + X + 1`.
pub fn coefficients(gamma: F128, r: &[F128], eq: &[F128]) -> Vec<F128> {
    let (beta, d) = frobenius_constants();
    assert!(r.len() == 7 && eq.len() == WORD);
    return (0..WORD)
        .map(|j| {
            // Σ_t eq(r, t)·X^(127−t) factorises over the bits of t.
            let top = (0..7).fold(gamma, |acc, i| acc * (r[i] + (F128::ONE + r[i]) * beta[(j + i) % WORD]));
            let b = beta[j];
            let low7 = (0..7).fold(F128::ZERO, |acc, t| acc * b + eq[t]);
            let low2 = eq[0] * b + eq[1];
            d[j] * (top + gamma * (low7 + low2 + eq[0]))
        })
        .collect();
}

/// `Σ_j gamma^j·eq(rho^(2^-j), x)` over the 128 inverse Frobenius powers of `rho`, without a
/// square root: the sum's `2^127`-th power is a chain of squarings over `Π_i (1 + rho_i +
/// x_i^(2^j))`.
pub fn twisted_eq(gamma: F128, rho: &[F128], x: &[F128]) -> F128 {
    let mut powers = x.to_vec();
    let (mut g, mut e, mut acc) = (gamma, F128::ONE, F128::ZERO);
    for j in 0..WORD {
        if j > 0 {
            powers.iter_mut().for_each(|p| *p = *p * *p);
            // e_j = gamma^(j·2^j), from e_(j−1) and gamma^(2^j).
            g = g * g;
            e = e * e * g;
        }
        let eq = rho.iter().zip(&powers).fold(F128::ONE, |a, (&p, &q)| a * (F128::ONE + p + q));
        acc = acc * acc + e * eq;
    }
    return acc * acc;
}

/// `Σ_j c_j·v_j^(2^j)`.
pub fn frobenius_sum(c: &[F128], v: &[F128]) -> F128 {
    return c.iter().zip(v).enumerate().fold(F128::ZERO, |acc, (j, (&c, &v))| {
        let mut p = v;
        for _ in 0..j {
            p = p * p;
        }
        acc + c * p
    });
}

/// The square root `v^(2^127)`.
fn sqrt(v: F128) -> F128 {
    let mut p = v;
    for _ in 0..WORD - 1 {
        p = p * p;
    }
    return p;
}

/// Where a transport's square-root chains come from.
pub enum Roots<'a> {
    /// Computed, and appended to the encoding being made.
    Derive(&'a mut Vec<u8>),
    /// Read from the encoding.
    Read,
}

/// `Σ_j c_j·v_j^(2^j)` for the coefficients `c` of [`coefficients`] at `gamma` and `r`, without the
/// coefficients: `c_j^(2^-j)` has the closed form of `c_0` at the `2^j`-th roots of `gamma` and
/// `r`, so the sum is a chain of squarings over `c_j^(2^-j)·v_j`. The roots, 127 levels of the
/// seven coordinates' then `gamma`'s, are checked by squaring each level into the one before.
pub fn rooted_sum(gamma: F128, r: &[F128], v: &[F128], rd: &mut Reader, roots: &mut Roots) -> Result<F128> {
    let (beta, d) = frobenius_constants();
    let x = beta[0];
    let mut levels: Vec<Vec<F128>> = vec![r.iter().copied().chain([gamma]).collect()];
    for j in 1..WORD {
        let level: Vec<F128> = match roots {
            Roots::Derive(out) => {
                let level: Vec<F128> = levels[j - 1].iter().map(|&s| sqrt(s)).collect();
                for &s in &level {
                    out.extend_from_slice(&(((s.hi as u128) << 64) | s.lo as u128).to_be_bytes());
                }
                level
            }
            Roots::Read => read_n(rd, 8)?,
        };
        if level.iter().zip(&levels[j - 1]).any(|(&s, &prev)| s * s != prev) {
            return Err(Reject("square roots"));
        }
        levels.push(level);
    }
    let mut acc = F128::ZERO;
    for j in (0..WORD).rev() {
        let (s, g) = (&levels[j][..7], levels[j][7]);
        let top = (0..7).fold(F128::ONE, |a, i| a * (s[i] + (F128::ONE + s[i]) * beta[i]));
        let high = (3..7).fold(F128::ONE, |a, i| a * (F128::ONE + s[i]));
        let e = build_eq_table(&s[..3]);
        let low7 = (0..7).fold(F128::ZERO, |a, t| a * x + e[t]);
        let low = high * (low7 + e[0] * x + e[1] + e[0]);
        acc = acc * acc + d[0] * g * (top + low) * v[j];
    }
    return Ok(acc);
}

/// `Π_l eq(bit_l(t), point[stride·l + offset])` over `layers` layers.
fn eq_at_integer(t: u64, point: &[F128], offset: usize, layers: usize) -> F128 {
    return (0..layers).fold(F128::ONE, |acc, l| {
        let p = point[2 * l + offset];
        acc * if t >> l & 1 == 1 { p } else { F128::ONE + p }
    });
}

/// The branching program's value over the boundary bits at `sigma`, for the rows `z_row` and the
/// dense index `index`.
fn boundary(z_row: &[F128], index: &[F128], sigma: &[F128], m: usize) -> F128 {
    let sparse = assist_sparse_transitions();
    let bit = |p: &[F128], l: usize| p.get(l).copied().unwrap_or(F128::ZERO);
    let mut g = [F128::ZERO; 4];
    g[STATE_SUCCESS] = F128::ONE;
    for layer in (0..=m).rev() {
        let eq4 = build_eq_table(&[bit(z_row, layer), bit(index, layer)]);
        let (rc, rd) = (sigma[2 * layer], sigma[2 * layer + 1]);
        let e = [(F128::ONE + rc) * (F128::ONE + rd), rc * (F128::ONE + rd), (F128::ONE + rc) * rd, rc * rd];
        let mut prev = [F128::ZERO; 4];
        for (cd, &ecd) in e.iter().enumerate() {
            for (s, slot) in prev.iter_mut().enumerate() {
                let ((i0, o0), (i1, o1)) = (sparse[cd][s][0], sparse[cd][s][1]);
                *slot += ecd * (eq4[i0] * g[o0] + eq4[i1] * g[o1]);
            }
        }
        g = prev;
    }
    return g[STATE_INITIAL];
}

/// What the transport leaves: the point of the committed stack and its claimed value there.
pub struct Opened {
    /// The point over the stack's words.
    pub point: Vec<F128>,
    /// The stack's claimed value at the point.
    pub value: F128,
    /// What the claims' weights must come to at the point, times the value.
    pub target: F128,
    /// The claims' weights at the point, as the assist proves them.
    pub weight: F128,
}

/// One ring switch: the claim against the sliced message, and the switched claim with the
/// equality table of its point.
fn ring_switch(rd: &mut Reader, tr: &mut KeccakChallenger, z: F128, x0: F128, value: F128) -> Result<(Vec<F128>, Vec<F128>, F128)> {
    tr.observe_label(b"flock-ring-switch-v0");
    let s = read_n(rd, WORD)?;
    tr.observe_f128_slice(&s);
    let skip = lagrange_weights_naive(6, z);
    let check = (0..64).fold(F128::ZERO, |acc, i| acc + skip[i] * (s[i] + x0 * (s[i] + s[64 + i])));
    if check != value {
        return Err(Reject("ring switch claim"));
    }
    let r = pow_vec(tr, rd.nonce()?, 3, 7)?;
    let eq = build_eq_table(&r);
    // Σ_b eq[b]·(the word whose bit i is bit b of s[i]) = Σ_i x^i·(Σ_b bit_b(s[i])·eq[b]).
    let x = F128::new(2, 0);
    let sum = s.iter().rev().fold(F128::ZERO, |acc, v| {
        let l = (0..WORD).fold(F128::ZERO, |a, b| {
            let set = if b < 64 { v.lo >> b & 1 } else { v.hi >> (b - 64) & 1 };
            if set == 1 { a + eq[b] } else { a }
        });
        acc * x + l
    });
    return Ok((r, eq, sum));
}

/// The sums of `table` over the layout's runs of columns.
fn run_sums(vk: &Vk, table: &[F128]) -> Vec<F128> {
    return vk.runs.iter().map(|run| table[run.start..run.start + run.len].iter().fold(F128::ZERO, |a, &b| a + b)).collect();
}

/// The merged transport of the claims `p` leaves, up to the opening of the committed stack; the
/// assist runs on a fork of `tr`, which is returned for merging after that opening.
pub fn transport(vk: &Vk, rd: &mut Reader, tr: &mut KeccakChallenger, p: &Piops, roots: &mut Roots) -> Result<(Opened, KeccakChallenger)> {
    let m = vk.dense_log;
    tr.observe_label(b"flock-merged-open-v1");
    let mut switched = Vec::with_capacity(2);
    for c in &p.bits {
        switched.push(ring_switch(rd, tr, c.z, c.x0, c.value)?);
    }
    for w in &p.words {
        tr.observe_f128(w.value);
    }
    p.gather.iter().for_each(|&v| tr.observe_f128(v));
    let n_direct = 2 + p.gather.len();
    let gammas = pow_vec(tr, rd.nonce()?, 6, 2 + n_direct)?;
    let (g_bits, g_direct) = gammas.split_at(2);
    let (g_words, g_gather) = g_direct.split_at(2);
    let mut running = F128::ZERO;
    for ((_, _, sum), &g) in switched.iter().zip(g_bits) {
        running += g * *sum;
    }
    running += g_words[0] * p.words[0].value + g_words[1] * p.words[1].value + dot(g_gather, &p.gather);
    let mut rho = Vec::with_capacity(m);
    for _ in 0..m {
        let (g1, ginf) = (rd.f128()?, rd.f128()?);
        tr.observe_f128(g1);
        tr.observe_f128(ginf);
        let r = pow_f128(tr, rd.nonce()?, 2)?;
        running = quadratic(running, g1, ginf, r);
        rho.push(r);
    }
    let q_eval = rd.f128()?;
    trace::mark(6, tr);
    // The statements' rows must differ: Flock merges equal ones, which this verifier does not.
    let rows = [&p.bits[0].row, &p.bits[1].row, &p.words[0].row, &p.gather_row];
    if (0..4).any(|i| (0..i).any(|j| rows[i] == rows[j])) || p.words[0].row != p.words[1].row {
        return Err(Reject("coinciding row points"));
    }

    let mut ch = tr.fork(b"flock-par-assist-v1");
    ch.observe_label(b"flock-multipoint-twisted-v1");
    let values = [read_n(rd, WORD)?, read_n(rd, WORD)?];
    let groups = read_n(rd, 2)?;
    values.iter().flatten().chain(&groups).for_each(|&v| ch.observe_f128(v));
    let n_values = 2 * WORD + 2;
    let gamma = pow_f128(&mut ch, rd.nonce()?, usize::BITS - (n_values - 1).leading_zeros())?;
    let mut gpow = Vec::with_capacity(n_values);
    let mut power = F128::ONE;
    for _ in 0..n_values {
        gpow.push(power);
        power *= gamma;
    }
    let mut claim = dot(&gpow[..WORD], &values[0]) + dot(&gpow[WORD..2 * WORD], &values[1]) + dot(&gpow[2 * WORD..], &groups);
    let mut point = Vec::with_capacity(m);
    for _ in 0..m {
        let (g1, ginf) = (rd.f128()?, rd.f128()?);
        ch.observe_f128(g1);
        ch.observe_f128(ginf);
        let r = pow_f128(&mut ch, rd.nonce()?, 2)?;
        claim = quadratic(claim, g1, ginf, r);
        point.push(r);
    }
    let g_at = twisted_eq(gamma, &rho, &point);
    let e_at = rho.iter().zip(&point).fold(F128::ONE, |acc, (&a, &b)| acc * (F128::ONE + a + b));

    trace::mark(7, &ch);
    ch.observe_label(b"flock-frobenius-assist-v0");
    let v = rd.f128()?;
    ch.observe_f128(v);
    let mut anchor = v;
    let mut sigma = Vec::with_capacity(2 * (m + 1));
    for _ in 0..2 * (m + 1) {
        let (g1, ginf) = (rd.f128()?, rd.f128()?);
        ch.observe_f128(g1);
        ch.observe_f128(ginf);
        let r = pow_f128(&mut ch, rd.nonce()?, 2)?;
        anchor = quadratic(anchor, g1, ginf, r);
        sigma.push(r);
    }
    let at_runs: Vec<F128> =
        vk.runs.iter().map(|run| eq_at_integer(run.t0, &sigma, 0, m + 1) * eq_at_integer(run.t1, &sigma, 1, m + 1)).collect();
    let mut expect = F128::ZERO;
    for (i, c) in p.bits.iter().enumerate() {
        let w = dot(&run_sums(vk, &build_eq_table(&c.col)), &at_runs);
        expect += gpow[WORD * i] * g_at * w * boundary(&c.row, &point, &sigma, m);
    }
    let cols: Vec<F128> = build_eq_table(&p.words[0].col)
        .iter()
        .zip(build_eq_table(&p.words[1].col))
        .map(|(&a, b)| g_words[0] * a + g_words[1] * b)
        .collect();
    let w = dot(&run_sums(vk, &cols), &at_runs);
    expect += gpow[2 * WORD] * e_at * w * boundary(&p.words[0].row, &point, &sigma, m);
    let mut hot = vec![F128::ZERO; 1 << vk.k_cols];
    for (&col, &g) in vk.gate_cols.iter().zip(g_gather) {
        hot[col] += g;
    }
    let w = dot(&run_sums(vk, &hot), &at_runs);
    expect += gpow[2 * WORD + 1] * e_at * w * boundary(&p.gather_row, &point, &sigma, m);
    if anchor != expect {
        return Err(Reject("layout assist"));
    }
    if claim != v {
        return Err(Reject("multipoint assist"));
    }
    let mut weight = groups[0] + groups[1];
    for ((r, eq, _), (&g, v)) in switched.iter().zip(g_bits.iter().zip(&values)) {
        let sum = rooted_sum(g, r, v, rd, roots)?;
        debug_assert_eq!(sum, frobenius_sum(&coefficients(g, r, eq), v));
        weight += sum;
    }
    return Ok((
        Opened {
            point: rho,
            value: q_eval,
            target: running,
            weight,
        },
        ch,
    ));
}
