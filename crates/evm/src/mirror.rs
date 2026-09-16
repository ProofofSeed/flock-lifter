// SPDX-License-Identifier: LGPL-3.0-or-later

//! A verifier for one chunk proof that reads the calldata encoding with a single forward cursor
//! and follows, step for step, the computation the contract performs.
//!
//! It is the contract's oracle: every value the contract derives can be compared with the value
//! derived here, and this verifier is itself checked against the lifter's own, which calls
//! Flock's. Flock's public helpers are used where the contract computes the same function;
//! Flock's crate-private Ligerito verifier is transcribed.

use flock_prover::{
    challenger::Challenger,
    field::{F128, F256},
    lincheck::build_eq_table,
    pcs::{
        ligerito::{VerifierConfig, eval_sk_at_vks},
        ring_switch::{
            build_claim_weights_from_skip, eval_rs_eq_finish_from_prefix_binary_q_f256, eval_rs_eq_prefix_f256,
            tensor_algebra_transpose,
        },
        stratified::LevelSchedule,
    },
    zerocheck::{
        multilinear::{interpolate_at_z_combined, interpolate_at_z_on_lambda, lagrange_weights_naive},
        univariate_skip_optimized::{medium_challenges_ghash, small_challenges_ghash},
    },
};
use pofseed_flock_lift::{
    chunk_rm::{pcs_params, statement_digest},
    matrix::{self, ExplicitClaim},
    transcript::KeccakChallenger,
};
use pofseed_flock_lift_block::{
    committed::LOOKUP_BITS,
    layout::{IO_BASE_WORD, IO_WORDS},
    program::Program,
};
use sha2::{Digest, Sha256};

use crate::calldata::{K_LOG, chunk_m};

/// Univariate-skip variables.
const K_SKIP: usize = 6;

/// Why the mirror refused a chunk proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reject(pub &'static str);

type Result<T> = core::result::Result<T, Reject>;

/// A forward cursor over calldata.
pub struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    /// A cursor at the start of `data`.
    pub fn new(data: &'a [u8]) -> Self {
        return Self { data, pos: 0 };
    }

    /// Bytes not yet read.
    pub fn remaining(&self) -> usize {
        return self.data.len() - self.pos;
    }

    /// The next `n` bytes.
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        if self.remaining() < n {
            return Err(Reject("calldata too short"));
        }
        let out = &self.data[self.pos..self.pos + n];
        self.pos += n;
        return Ok(out);
    }

    /// A big-endian field element.
    pub fn f128(&mut self) -> Result<F128> {
        let v = u128::from_be_bytes(self.take(16)?.try_into().expect("sixteen bytes"));
        return Ok(F128::new(v as u64, (v >> 64) as u64));
    }

    /// A field element in Flock's native layout.
    pub fn f128_native(&mut self) -> Result<F128> {
        let b = self.take(16)?;
        return Ok(native(b));
    }

    /// An extension element, `c1` then `c0`.
    pub fn f256(&mut self) -> Result<F256> {
        let c1 = self.f128()?;
        let c0 = self.f128()?;
        return Ok(F256::new(c0, c1));
    }

    /// A 32-byte hash.
    pub fn hash(&mut self) -> Result<[u8; 32]> {
        return Ok(self.take(32)?.try_into().expect("thirty-two bytes"));
    }

    /// A proof-of-work nonce.
    pub fn nonce(&mut self) -> Result<u64> {
        return Ok(u64::from_be_bytes(self.take(8)?.try_into().expect("eight bytes")));
    }

    /// A big-endian `u32`.
    pub fn u32(&mut self) -> Result<u32> {
        return Ok(u32::from_be_bytes(self.take(4)?.try_into().expect("four bytes")));
    }
}

/// A field element from sixteen bytes in Flock's native layout.
pub fn native(b: &[u8]) -> F128 {
    return F128::new(
        u64::from_le_bytes(b[..8].try_into().expect("eight bytes")),
        u64::from_le_bytes(b[8..16].try_into().expect("eight bytes")),
    );
}

const fn bits_for(n: usize) -> u32 {
    return usize::BITS - n.leading_zeros();
}

fn pow_f128(tr: &mut KeccakChallenger, nonce: u64, bits: u32) -> Result<F128> {
    return tr.verify_pow_and_sample_f128(nonce, bits).ok_or(Reject("proof of work"));
}

fn pow_vec(tr: &mut KeccakChallenger, nonce: u64, bits: u32, n: usize) -> Result<Vec<F128>> {
    return tr.verify_pow_and_sample_f128_vec(nonce, bits, n).ok_or(Reject("proof of work"));
}

fn dot(a: &[F128], b: &[F128]) -> F128 {
    return a.iter().zip(b).fold(F128::ZERO, |acc, (&x, &y)| acc + x * y);
}

/// An evaluation claim on the committed witness: a skip point, the remaining coordinates in
/// address order, and the value.
#[derive(Clone, Debug)]
pub struct Claim {
    /// The univariate-skip point.
    pub z: F128,
    /// The `m − 6` multilinear coordinates.
    pub x: Vec<F128>,
    /// The claimed value.
    pub value: F128,
}

/// What the zerocheck hands on.
struct Zerocheck {
    z: F128,
    mlv: Vec<F128>,
    r_rest: Vec<F128>,
    a: F128,
    b: F128,
    c: F128,
}

fn zerocheck(m: usize, rd: &mut Reader, tr: &mut KeccakChallenger) -> Result<Zerocheck> {
    tr.observe_label(b"flock-zerocheck-v0");
    let n0 = rd.nonce()?;
    let r_skip = pow_vec(tr, n0, bits_for(m), K_SKIP)?;
    let r_outer = tr.sample_f128_vec(m - K_SKIP - 7);
    let mut r = r_skip;
    r.extend_from_slice(&small_challenges_ghash());
    r.extend_from_slice(&medium_challenges_ghash());
    r.extend_from_slice(&r_outer);
    let ab: Vec<F128> = (0..1 << K_SKIP).map(|_| rd.f128()).collect::<Result<_>>()?;
    let c: Vec<F128> = (0..1 << K_SKIP).map(|_| rd.f128()).collect::<Result<_>>()?;
    tr.observe_f128_slice(&ab);
    tr.observe_f128_slice(&c);
    let n1 = rd.nonce()?;
    let z = pow_f128(tr, n1, bits_for((1 << (K_SKIP + 1)) - 1))?;
    let final_c = rd.f128()?;
    let c_eval = interpolate_at_z_on_lambda(&c, K_SKIP, z);
    if c_eval != final_c {
        return Err(Reject("zerocheck c evaluation"));
    }
    let combined: Vec<F128> = ab.iter().zip(&c).map(|(&x, &y)| x + y).collect();
    let mut running = interpolate_at_z_combined(&combined, K_SKIP, z) + c_eval;
    let mut mlv = Vec::with_capacity(m - K_SKIP);
    for i in 0..m - K_SKIP {
        let (e1, einf, n) = (rd.f128()?, rd.f128()?, rd.nonce()?);
        let r_eq = r[K_SKIP + i];
        let g0 = (running + r_eq * e1) * (F128::ONE + r_eq).inv();
        tr.observe_f128(e1);
        tr.observe_f128(einf);
        let rho = pow_f128(tr, n, bits_for(2))?;
        mlv.push(rho);
        let one_rho = F128::ONE + rho;
        running = g0 * one_rho + e1 * rho + einf * rho * one_rho;
    }
    let (a, b) = (rd.f128()?, rd.f128()?);
    if running != a * b {
        return Err(Reject("zerocheck final"));
    }
    tr.observe_f128(a);
    tr.observe_f128(b);
    return Ok(Zerocheck {
        z,
        mlv,
        r_rest: r[K_SKIP..].to_vec(),
        a,
        b,
        c: c_eval,
    });
}

/// The lincheck's matrix claim: the equation the matrix discharge must close.
#[derive(Clone, Debug)]
pub struct MatrixClaim {
    /// The A-side batching challenge.
    pub alpha: F128,
    /// The constant-wire pin challenge.
    pub beta: F128,
    /// Row weights on the skipped variables.
    pub skip_weights: Vec<F128>,
    /// The row point after the skip, LSB-first.
    pub x_inner_rest: Vec<F128>,
    /// The column point after the skip, LSB-first.
    pub r_inner_rest: Vec<F128>,
    /// The collapsed witness the combination is paired with.
    pub z_partial: Vec<F128>,
    /// The running sumcheck claim the pairing must equal.
    pub running: F128,
}

impl MatrixClaim {
    /// Whether `comb`, the discharged combination, closes the equation.
    pub fn closes(&self, comb: &[F128]) -> bool {
        return dot(comb, &self.z_partial) == self.running;
    }
}

fn lincheck(
    rd: &mut Reader,
    tr: &mut KeccakChallenger,
    zc: &Zerocheck,
) -> Result<(MatrixClaim, Claim)> {
    let inner = K_LOG - K_SKIP;
    tr.observe_label(b"flock-lincheck-v0");
    let (na, nb) = (rd.nonce()?, rd.nonce()?);
    let alpha = pow_f128(tr, na, 1)?;
    let beta = pow_f128(tr, nb, 1)?;
    let mut running = alpha * zc.a + zc.b + beta;
    let mut r_rounds = Vec::with_capacity(inner);
    for _ in 0..inner {
        let (e1, einf, n) = (rd.f128()?, rd.f128()?, rd.nonce()?);
        tr.observe_f128(e1);
        tr.observe_f128(einf);
        let r = pow_f128(tr, n, 2)?;
        let e0 = running + e1;
        let c1 = e0 + e1 + einf;
        running = einf * r * r + c1 * r + e0;
        r_rounds.push(r);
    }
    let z_partial: Vec<F128> = (0..1 << K_SKIP).map(|_| rd.f128()).collect::<Result<_>>()?;
    tr.observe_f128_slice(&z_partial);
    r_rounds.reverse();
    let n = rd.nonce()?;
    let z2 = pow_f128(tr, n, K_SKIP as u32)?;
    let w = dot(&lagrange_weights_naive(K_SKIP, z2), &z_partial);
    let mut x = r_rounds.clone();
    x.extend_from_slice(&zc.mlv[inner..]);
    return Ok((
        MatrixClaim {
            alpha,
            beta,
            skip_weights: lagrange_weights_naive(K_SKIP, zc.z),
            x_inner_rest: zc.mlv[..inner].to_vec(),
            r_inner_rest: r_rounds,
            z_partial,
            running,
        },
        Claim { z: z2, x, value: w },
    ));
}

/// The published-word claim, with its value computed from the published words.
fn io_claim(tr: &mut KeccakChallenger, rows: &[Vec<F128>], nu: usize) -> Claim {
    let z = tr.sample_f128();
    let r6 = tr.sample_f128();
    let r_word: Vec<F128> = (0..4).map(|_| tr.sample_f128()).collect();
    let x_outer: Vec<F128> = (0..nu).map(|_| tr.sample_f128()).collect();
    let mut x = vec![r6];
    x.extend_from_slice(&r_word);
    for bit in 11..K_LOG {
        let set = ((IO_BASE_WORD * 128) >> bit) & 1 == 1;
        x.push(if set { F128::ONE } else { F128::ZERO });
    }
    x.extend_from_slice(&x_outer);
    let skip = lagrange_weights_naive(K_SKIP, z);
    let bit_w: Vec<F128> = (0..128)
        .map(|b| skip[b & 63] * if b >> 6 == 0 { F128::ONE + r6 } else { r6 })
        .collect();
    let e_word = build_eq_table(&r_word);
    let e_row = build_eq_table(&x_outer);
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
    return Claim { z, x, value };
}

#[derive(Clone, Copy)]
struct Quad {
    c: F256,
    b: F256,
    a: F256,
}

impl Quad {
    fn from_msg(u0: F256, u2: F256, claim: F256) -> Self {
        return Self {
            c: u0,
            b: claim + u2,
            a: u2,
        };
    }

    fn eval(self, r: F256) -> F256 {
        return self.c + r * self.b + (r * r) * self.a;
    }

    fn fold(self, rhs: Self, alpha: F128) -> Self {
        return Self {
            c: self.c + rhs.c * alpha,
            b: self.b + rhs.b * alpha,
            a: self.a + rhs.a * alpha,
        };
    }
}

fn message(rd: &mut Reader, tr: &mut KeccakChallenger) -> Result<(F256, F256)> {
    let (u0, u2) = (rd.f256()?, rd.f256()?);
    tr.observe_f256(u0);
    tr.observe_f256(u2);
    return Ok((u0, u2));
}

fn ceil_log2(n: usize) -> usize {
    return if n <= 1 { 0 } else { (n - 1).ilog2() as usize + 1 };
}

fn queries(tr: &mut KeccakChallenger, nonce: u64, bits: u32, block_len: usize, s: &LevelSchedule) -> Result<Vec<usize>> {
    let count = s.queries();
    let words = pow_vec(tr, nonce, bits, count)?;
    let d = block_len.trailing_zeros() as usize;
    return Ok(s
        .query_strata()
        .zip(&words)
        .map(|((c, stratum), v)| (stratum << (d - c)) | ((v.lo as usize) & ((1usize << (d - c)) - 1)))
        .collect());
}

fn sha_pair(l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(l);
    h.update(r);
    return h.finalize().into();
}

/// Reads a level's opened rows and paths and checks them against its cap.
fn opens(
    rd: &mut Reader,
    cap: &[[u8; 32]],
    block_len: usize,
    qs: &[usize],
    width: usize,
    s: &LevelSchedule,
) -> Result<Vec<Vec<F128>>> {
    let d = block_len.trailing_zeros() as usize;
    let c1 = s.cap_depth();
    if s.log_block_len != d || cap.len() != 1 << c1 {
        return Err(Reject("level shape"));
    }
    let mut rows = Vec::with_capacity(qs.len());
    let mut leaves = Vec::with_capacity(qs.len());
    for _ in qs {
        let bytes = rd.take(16 * width)?;
        leaves.push(<[u8; 32]>::from(Sha256::digest(bytes)));
        rows.push(bytes.chunks(16).map(native).collect::<Vec<_>>());
    }
    for (&q, leaf) in qs.iter().zip(leaves) {
        let mut acc = leaf;
        let mut idx = q;
        for _ in 0..d - c1 {
            let sib = rd.hash()?;
            acc = if idx & 1 == 0 { sha_pair(&acc, &sib) } else { sha_pair(&sib, &acc) };
            idx >>= 1;
        }
        if acc != cap[idx] {
            return Err(Reject("merkle path"));
        }
    }
    return Ok(rows);
}

fn induce_enforced_sum(rows: &[Vec<F128>], lanes: &[F256], alpha: &[F128]) -> F256 {
    let lane_w = eq256(lanes);
    let row_w = build_eq_table(alpha);
    return rows.iter().zip(&row_w).fold(F256::ZERO, |acc, (row, &rw)| {
        acc + row.iter().zip(&lane_w).fold(F256::ZERO, |a, (&w, &l)| a + l * w) * rw
    });
}

fn eq256(point: &[F256]) -> Vec<F256> {
    let mut t = vec![F256::ONE];
    for &x in point {
        let lo: Vec<F256> = t.iter().map(|&e| e * (F256::ONE + x)).collect();
        let hi: Vec<F256> = t.iter().map(|&e| e * x).collect();
        t = lo;
        t.extend(hi);
    }
    return t;
}

fn coordinate_fold_factor(challenge: F256) -> F256 {
    return F256::ONE + challenge * (F256::ONE + F256::U);
}

fn original_challenges(initial: &[F256], levels: &[Vec<F256>], start: usize) -> Vec<F256> {
    let mut out = Vec::new();
    if start == 0 {
        out.extend_from_slice(initial);
    }
    for level in &levels[start..] {
        out.extend_from_slice(&level[1..]);
    }
    return out;
}

fn factor_product(levels: &[Vec<F256>], start: usize) -> F256 {
    return levels[start..].iter().fold(F256::ONE, |acc, l| acc * coordinate_fold_factor(l[0]));
}

fn eq_residual(point: &[F128], fixed: &[F256], residual_log: usize, scale: F256) -> Vec<F256> {
    let prefix = point[..fixed.len()]
        .iter()
        .zip(fixed)
        .fold(scale, |acc, (&z, &r)| acc * (F256::ONE + F256::from(z) + r));
    return (0..1usize << residual_log)
        .map(|y| {
            point[fixed.len()..].iter().enumerate().fold(prefix, |acc, (j, &z)| {
                acc * if (y >> j) & 1 == 1 { z } else { F128::ONE + z }
            })
        })
        .collect();
}

fn induced_basis_at_residual(log_cols: usize, qs: &[usize], alpha: &[F128], fixed: &[F256], residual_log: usize) -> Vec<F256> {
    let sks = eval_sk_at_vks(log_cols);
    let inv: Vec<F128> = sks.iter().map(|&v| if v.is_zero() { F128::ZERO } else { v.inv() }).collect();
    let weights = build_eq_table(alpha);
    let per_query: Vec<(F128, F256, Vec<F128>)> = qs
        .iter()
        .zip(&weights)
        .map(|(&q, &weight)| {
            let mut w = vec![F128::ZERO; log_cols];
            if log_cols > 0 {
                w[0] = F128::new(q as u64, 0);
                for k in 1..log_cols {
                    w[k] = w[k - 1] * w[k - 1] + sks[k - 1] * w[k - 1];
                }
                for k in 0..log_cols {
                    w[k] *= inv[k];
                }
            }
            let prefix = fixed
                .iter()
                .zip(&w)
                .fold(F256::ONE, |acc, (&p, &wk)| acc * (F256::ONE + p * (F128::ONE + wk)));
            (weight, prefix, w[fixed.len()..].to_vec())
        })
        .collect();
    return (0..1usize << residual_log)
        .map(|y| {
            per_query.iter().fold(F256::ZERO, |sum, (weight, prefix, suffix)| {
                let tail = suffix.iter().enumerate().fold(F256::ONE, |acc, (j, &wk)| {
                    if (y >> j) & 1 == 0 { acc } else { acc * F256::from(wk) }
                });
                sum + *prefix * tail * *weight
            })
        })
        .collect();
}

struct Consistency {
    log_cols: usize,
    queries: Vec<usize>,
    alpha: Vec<F128>,
    beta: F128,
    start: usize,
}

struct Ood {
    point: Vec<F128>,
    beta: F128,
    split: Option<usize>,
}

fn read_cap(rd: &mut Reader, s: &LevelSchedule) -> Result<Vec<[u8; 32]>> {
    return (0..1usize << s.cap_depth()).map(|_| rd.hash()).collect();
}

#[allow(clippy::too_many_arguments)]
fn ligerito(
    config: &VerifierConfig,
    log_n: usize,
    rd: &mut Reader,
    tr: &mut KeccakChallenger,
    target: F128,
    cap0: &[[u8; 32]],
    residual_fn: impl Fn(&[F256], usize) -> Vec<F256>,
) -> Result<()> {
    let initial_k = config.initial_k;
    let rounds = config.recursive_steps;
    let s = &config.stratified;
    let claim_bits = |l: usize| config.claim_batch_grinding_bits[l] as u32;
    let consistency_bits = |l: usize| config.consistency_batch_grinding_bits[l] as u32;
    assert!(rounds >= 1 && config.recursive_ks.iter().all(|&k| k >= 2));
    assert!(config.fold_grinding_bits.iter().all(|&b| b == 0));
    tr.observe_label(b"flock-ligerito-basis-f256-split-v0");
    tr.observe_f128(target);
    tr.observe_bytes(cap0.as_flattened());
    let block_len_0 = 1usize << (log_n - initial_k + config.log_inv_rates[0]);
    let mut claim = F256::from(target);
    let mut oods = Vec::new();
    for _ in 0..config.ood_samples[0] {
        let point = tr.sample_f128_vec(log_n);
        let y = rd.f128()?;
        tr.observe_f128(y);
        let beta = pow_f128(tr, rd.nonce()?, claim_bits(0))?;
        claim += F256::from(beta * y);
        oods.push(Ood { point, beta, split: None });
    }
    let (u0, u2) = message(rd, tr)?;
    let mut quad = Quad::from_msg(u0, u2, claim);
    let mut initial = Vec::with_capacity(initial_k);
    for _ in 0..initial_k {
        let ch = tr.sample_f256();
        claim = quad.eval(ch);
        initial.push(ch);
        let (u0, u2) = message(rd, tr)?;
        quad = Quad::from_msg(u0, u2, claim);
    }
    let mut split_dim = log_n - initial_k + 1;
    let cap1 = read_cap(rd, &s[1])?;
    tr.observe_bytes(cap1.as_flattened());
    for _ in 0..config.ood_samples[1] {
        let point = tr.sample_f128_vec(split_dim);
        let y = rd.f128()?;
        tr.observe_f128(y);
        let (u0, u2) = message(rd, tr)?;
        let intro = Quad::from_msg(u0, u2, F256::from(y));
        let beta = pow_f128(tr, rd.nonce()?, claim_bits(1))?;
        quad = quad.fold(intro, beta);
        claim += F256::from(beta * y);
        oods.push(Ood { point, beta, split: Some(0) });
    }
    let qn = rd.nonce()?;
    let qs0 = queries(tr, qn, config.grinding_bits[0] as u32, block_len_0, &s[0])?;
    let cn = rd.nonce()?;
    let alpha0 = pow_vec(tr, cn, consistency_bits(0), ceil_log2(config.queries[0]))?;
    let rows0 = opens(rd, cap0, block_len_0, &qs0, 1 << initial_k, &s[0])?;
    let enforced0 = induce_enforced_sum(&rows0, &initial, &alpha0);
    let (u0, u2) = message(rd, tr)?;
    let intro = Quad::from_msg(u0, u2, enforced0);
    let beta0 = pow_f128(tr, rd.nonce()?, claim_bits(1))?;
    quad = quad.fold(intro, beta0);
    claim += enforced0 * beta0;
    let mut consistency = vec![Consistency {
        log_cols: log_n - initial_k,
        queries: qs0,
        alpha: alpha0,
        beta: beta0,
        start: 0,
    }];
    let mut levels: Vec<Vec<F256>> = Vec::with_capacity(rounds);
    let mut prev_cap = cap1;
    let mut prev_lanes = config.recursive_ks[0];
    let mut prev_cols = split_dim - prev_lanes;
    let mut prev_rate = config.log_inv_rates[1];
    for i in 0..rounds {
        let k = config.recursive_ks[i];
        let mut chs = Vec::with_capacity(k);
        for _ in 0..k {
            let ch = tr.sample_f256();
            claim = quad.eval(ch);
            chs.push(ch);
            let (u0, u2) = message(rd, tr)?;
            quad = Quad::from_msg(u0, u2, claim);
        }
        levels.push(chs);
        let ext = split_dim - k;
        let level = i + 1;
        let block_len = 1usize << (prev_cols + prev_rate);
        if i + 1 == rounds {
            let yr: Vec<F128> = (0..2usize << ext).map(|_| rd.f128()).collect::<Result<_>>()?;
            yr.iter().for_each(|&v| tr.observe_f128(v));
            let qn = rd.nonce()?;
            let qs = queries(tr, qn, config.grinding_bits[level] as u32, block_len, &s[level])?;
            let cn = rd.nonce()?;
            let alpha = pow_vec(tr, cn, consistency_bits(level), ceil_log2(config.queries[level]))?;
            let rows = opens(rd, &prev_cap, block_len, &qs, 1 << prev_lanes, &s[level])?;
            let enforced = induce_enforced_sum(&rows, &levels[i], &alpha);
            let beta = pow_f128(tr, rd.nonce()?, claim_bits(level))?;
            claim += enforced * beta;
            consistency.push(Consistency {
                log_cols: ext,
                queries: qs,
                alpha,
                beta,
                start: rounds,
            });
            let original = original_challenges(&initial, &levels, 0);
            assert_eq!(original.len() + ext, log_n);
            let mut residual = residual_fn(&original, ext);
            let scale0 = factor_product(&levels, 0);
            residual.iter_mut().for_each(|v| *v *= scale0);
            for o in &oods {
                let (fixed, scale) = match o.split {
                    None => (original.clone(), factor_product(&levels, 0)),
                    Some(sl) => {
                        let mut fixed = levels[sl].clone();
                        for later in &levels[sl + 1..] {
                            fixed.extend_from_slice(&later[1..]);
                        }
                        (fixed, factor_product(&levels, sl + 1))
                    }
                };
                for (d, v) in residual.iter_mut().zip(eq_residual(&o.point, &fixed, ext, scale * o.beta)) {
                    *d += v;
                }
            }
            for c in &consistency {
                let fixed = original_challenges(&[], &levels, c.start);
                let values = induced_basis_at_residual(c.log_cols, &c.queries, &c.alpha, &fixed, ext);
                let scale = factor_product(&levels, c.start) * c.beta;
                for (d, v) in residual.iter_mut().zip(values) {
                    *d += v * scale;
                }
            }
            let got = yr.chunks(2).zip(&residual).fold(F256::ZERO, |acc, (pair, &basis)| {
                acc + basis * pair[0] + (F256::U * basis) * pair[1]
            });
            if rd.remaining() != 0 {
                return Err(Reject("trailing calldata"));
            }
            return if got == claim { Ok(()) } else { Err(Reject("ligerito residual")) };
        }
        split_dim = ext + 1;
        let cap = read_cap(rd, &s[level + 1])?;
        tr.observe_bytes(cap.as_flattened());
        for _ in 0..config.ood_samples[level + 1] {
            let point = tr.sample_f128_vec(split_dim);
            let y = rd.f128()?;
            tr.observe_f128(y);
            let (u0, u2) = message(rd, tr)?;
            let intro = Quad::from_msg(u0, u2, F256::from(y));
            let beta = pow_f128(tr, rd.nonce()?, claim_bits(level + 1))?;
            quad = quad.fold(intro, beta);
            claim += F256::from(beta * y);
            oods.push(Ood {
                point,
                beta,
                split: Some(i + 1),
            });
        }
        let qn = rd.nonce()?;
        let qs = queries(tr, qn, config.grinding_bits[level] as u32, block_len, &s[level])?;
        let cn = rd.nonce()?;
        let alpha = pow_vec(tr, cn, consistency_bits(level), ceil_log2(config.queries[level]))?;
        let rows = opens(rd, &prev_cap, block_len, &qs, 1 << prev_lanes, &s[level])?;
        let enforced = induce_enforced_sum(&rows, &levels[i], &alpha);
        let (u0, u2) = message(rd, tr)?;
        let intro = Quad::from_msg(u0, u2, enforced);
        let beta = pow_f128(tr, rd.nonce()?, claim_bits(level + 1))?;
        quad = quad.fold(intro, beta);
        claim += enforced * beta;
        consistency.push(Consistency {
            log_cols: ext,
            queries: qs,
            alpha,
            beta,
            start: i + 1,
        });
        prev_cap = cap;
        prev_lanes = config.recursive_ks[i + 1];
        prev_cols = split_dim - prev_lanes;
        prev_rate = config.log_inv_rates[i + 2];
    }
    unreachable!("the last round returns");
}

fn opening(m: usize, rd: &mut Reader, tr: &mut KeccakChallenger, cap0: &[[u8; 32]], claims: &[Claim]) -> Result<()> {
    let log_n = m - 7;
    tr.observe_label(b"flock-pcs-open-batch-v0");
    let mut outs = Vec::with_capacity(claims.len());
    for c in claims {
        tr.observe_label(b"flock-ring-switch-v0");
        let s: Vec<F128> = (0..128).map(|_| rd.f128()).collect::<Result<_>>()?;
        tr.observe_f128_slice(&s);
        let weights = build_claim_weights_from_skip(&lagrange_weights_naive(K_SKIP, c.z), c.x[0]);
        if dot(&weights, &s) != c.value {
            return Err(Reject("ring switch claim"));
        }
        let rdp = pow_vec(tr, rd.nonce()?, 3, 7)?;
        let eq = build_eq_table(&rdp);
        let sum = dot(&tensor_algebra_transpose(&s), &eq);
        outs.push((sum, eq));
    }
    let gammas = if claims.len() == 1 {
        tr.sample_f128_vec(1)
    } else {
        pow_vec(tr, rd.nonce()?, 6, claims.len())?
    };
    let target = outs.iter().zip(&gammas).fold(F128::ZERO, |acc, ((sum, _), &g)| acc + g * *sum);
    let residual_fn = |ris: &[F256], yr_log: usize| -> Vec<F256> {
        let p = ris.len();
        let prefixes: Vec<_> = claims.iter().map(|c| eval_rs_eq_prefix_f256(&c.x[1..1 + p], ris)).collect();
        return (0..1u32 << yr_log)
            .map(|y| {
                claims.iter().zip(&prefixes).zip(&outs).zip(&gammas).fold(
                    F256::ZERO,
                    |acc, (((c, prefix), (_, eq)), &g)| {
                        acc + g * eval_rs_eq_finish_from_prefix_binary_q_f256(prefix, &c.x[1 + p..], y, eq)
                    },
                )
            })
            .collect();
    };
    let config = pcs_params(m).ligerito_verifier_config().expect("registered configuration");
    return ligerito(&config, log_n, rd, tr, target, cap0, residual_fn);
}

/// Verifies one chunk proof over the published words `publics` (one row per live block, in
/// native layout), returning the matrix claim its discharge must close.
pub fn verify_chunk(program: &Program, publics: &[Vec<F128>], domain: &[u8], data: &[u8]) -> Result<MatrixClaim> {
    let n = publics.len();
    let m = chunk_m(n);
    let nu = m - K_LOG;
    let mut rows = publics.to_vec();
    rows.resize(1 << nu, publics[n - 1].clone());
    let mut rd = Reader::new(data);
    let mut tr = KeccakChallenger::new(domain);
    tr.observe_label(b"pofseed-flock-lift-published-words");
    for row in &rows {
        row.iter().for_each(|&w| tr.observe_f128(w));
    }
    let config = pcs_params(m).ligerito_verifier_config().expect("registered configuration");
    let cap0 = read_cap(&mut rd, &config.stratified[0])?;
    tr.observe_label(b"flock-r1cs-v0");
    tr.observe_bytes(&statement_digest(program, nu));
    tr.observe_bytes(cap0.as_flattened());
    let zc = zerocheck(m, &mut rd, &mut tr)?;
    let (matrix, ab) = lincheck(&mut rd, &mut tr, &zc)?;
    let c = Claim {
        z: zc.z,
        x: zc.r_rest.clone(),
        value: zc.c,
    };
    let io = io_claim(&mut tr, &rows, nu);
    opening(m, &mut rd, &mut tr, &cap0, &[ab, c, io])?;
    return Ok(matrix);
}

fn read_n(rd: &mut Reader, n: usize) -> Result<Vec<F128>> {
    return (0..n).map(|_| rd.f128()).collect();
}

/// Verifies a matrix proof over `claims` against the committed entry list whose cap is `cap`,
/// reading the calldata encoding.
pub fn verify_matrix(log_len: usize, cap: &[[u8; 32]], claims: &[ExplicitClaim], domain: &[u8], data: &[u8]) -> Result<()> {
    let m = log_len + 6;
    let mut rd = Reader::new(data);
    let config = pcs_params(m).ligerito_verifier_config().expect("registered configuration");
    let cap0 = read_cap(&mut rd, &config.stratified[0])?;
    if cap0 != cap {
        return Err(Reject("entry commitment"));
    }
    let mut tr = KeccakChallenger::new(domain);
    matrix::observe_claims(&mut tr, claims);
    let mu = pow_f128(&mut tr, rd.nonce()?, matrix::MU_BITS)?;
    let weights = matrix::powers(mu, claims.len());
    let mut claim = claims.iter().zip(&weights).fold(F128::ZERO, |a, (c, &w)| a + c.value * w);
    let mut rho = Vec::with_capacity(log_len);
    for _ in 0..log_len {
        let msg = read_n(&mut rd, matrix::MAIN_DEGREE)?;
        tr.observe_f128_slice(&msg);
        let r = pow_f128(&mut tr, rd.nonce()?, matrix::MAIN_BITS)?;
        claim = matrix::horner(&matrix::expand(&msg, claim), r);
        rho.push(r);
    }
    let total: usize = (0..matrix::LOOKUPS).map(matrix::addresses).sum();
    let counts = read_n(&mut rd, total)?;
    let tables: Vec<_> = claims.iter().map(ExplicitClaim::tables).collect();
    if matrix::main_expected(&tables, &weights, &counts) != claim {
        return Err(Reject("matrix main sumcheck"));
    }
    tr.observe_f128_slice(&counts);
    let gamma = pow_f128(&mut tr, rd.nonce()?, matrix::LOOKUP_POINT_BITS)?;
    let points: Vec<Vec<F128>> = LOOKUP_BITS.iter().map(|&b| tr.sample_f128_vec(b)).collect();
    let gammas = matrix::powers(gamma, matrix::LOOKUPS);
    let mut claim = matrix::count_claim(&counts, &gammas, &points);
    let mut sigma = Vec::with_capacity(log_len);
    for _ in 0..log_len {
        let msg = read_n(&mut rd, matrix::COUNT_DEGREE)?;
        tr.observe_f128_slice(&msg);
        let r = pow_f128(&mut tr, rd.nonce()?, matrix::COUNT_BITS)?;
        claim = matrix::horner(&matrix::expand(&msg, claim), r);
        sigma.push(r);
    }
    let bits = read_n(&mut rd, matrix::ADDRESS_BITS)?;
    let eq = rho.iter().zip(&sigma).fold(F128::ONE, |a, (&x, &y)| a * (F128::ONE + x + y));
    if eq * matrix::count_sum(&gammas, &points, &bits) != claim {
        return Err(Reject("matrix count sumcheck"));
    }
    tr.observe_f128_slice(&bits);
    let zeta = pow_f128(&mut tr, rd.nonce()?, matrix::ZETA_BITS)?;
    let value = dot(&lagrange_weights_naive(K_SKIP, zeta), &bits);
    opening(m, &mut rd, &mut tr, &cap0, &[Claim { z: zeta, x: sigma, value }])?;
    if rd.remaining() != 0 {
        return Err(Reject("trailing calldata"));
    }
    return Ok(());
}
