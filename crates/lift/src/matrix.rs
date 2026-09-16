// SPDX-License-Identifier: LGPL-3.0-or-later

//! A proof that matrix claims' explicit-row parts are the table-weighted sums of a block's public
//! entry list, against a commitment to that list made once per statement.
//!
//! The list (`pofseed_flock_lift_block::committed`) has `2^n` entries, each reading eight small
//! per-claim tables. For claims `c` with tables `T_c` and values `V_c`, and a batching challenge
//! `μ`, the proof shows `Σ_c μ^c·V_c = Σ_k Σ_c μ^c·Π_l T_{c,l}[a_l(k)]`:
//!
//! 1. a degree-8 sumcheck over the entry index reduces the sum to the point `ρ`;
//! 2. the prover sends, per lookup `l`, the counts `ĉ_l[a] = Σ_k eq(ρ, k)·[a_l(k) = a]`, from
//!    which the verifier forms every `T̂_{c,l}(ρ) = Σ_a T_{c,l}[a]·ĉ_l[a]` itself;
//! 3. the counts are checked at random address points `r_l`, batched by `γ`: a degree-15
//!    sumcheck shows `Σ_l γ^l·Σ_a eq(r_l, a)·ĉ_l[a] = Σ_k eq(ρ, k)·Σ_l γ^l·Π_i (1 + r_{l,i} + A_{l,i}(k))`
//!    over the address bits `A` of the entries, reducing it to the point `σ`;
//! 4. the prover sends the address bits' extensions at `σ`, and one evaluation claim at
//!    `(σ, ζ)` on the committed list, whose bit positions form the skipped variables, is opened.
//!
//! Every challenge is ground so that its round-by-round error is at most `2^-128`.

use flock_prover::{
    challenger::Challenger,
    field::F128,
    lincheck::{QuirkyPoint, SkipPoint, build_eq_table},
    pcs::{
        BatchOpeningProofLigerito, Commitment, PcsParams, ProverData, commit,
        open_batch_mixed_ligerito_with_precomputed_s_hat_v_and_grinding,
    },
    proof::ZClaim,
    verifier::verify_claims_ligerito,
    zerocheck::PaddingSpec,
};
use pofseed_flock_lift_block::committed::{Entry, LOOKUP_BITS, P_COLS, P_ROWS, Tables, address};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::chunk_rm::pcs_params;

/// Lookups an entry makes.
const LOOKUPS: usize = LOOKUP_BITS.len();

/// Bit position of each lookup's address in a packed entry.
const OFFSETS: [usize; LOOKUPS] = [0, 1, 9, 17, 23, 31, 39, 45];

/// Address bits of all lookups together.
const ADDRESS_BITS: usize = 59;

/// Degree of the main sumcheck.
const MAIN_DEGREE: usize = LOOKUPS;

/// Degree of the count sumcheck: the `eq` factor and the widest address.
const COUNT_DEGREE: usize = 1 + 14;

/// Grinding bits of the claim batching, of each main round, of the count points, of each count
/// round, and of the opening's skip point.
const MU_BITS: u32 = 2;
const MAIN_BITS: u32 = 3;
const LOOKUP_POINT_BITS: u32 = 5;
const COUNT_BITS: u32 = 4;
const ZETA_BITS: u32 = 6;

/// Addresses a lookup can read: the prefix table uses `P_ROWS·P_COLS` of its `2^14`.
fn addresses(l: usize) -> usize {
    return if l == LOOKUPS - 1 { P_ROWS * P_COLS } else { 1 << LOOKUP_BITS[l] };
}

/// Entry-index bits a list is padded to at least, so that its commitment has a registered
/// Ligerito configuration.
const MIN_LOG_LEN: usize = 22;

/// The per-statement proving key: the padded entry list and its commitment.
pub struct MatrixKey {
    entries: Vec<Entry>,
    log_len: usize,
    packed: Vec<F128>,
    params: PcsParams,
    commitment: Commitment,
    prover_data: ProverData,
}

impl MatrixKey {
    /// Commits to `entries`, padded with entries that read zero to a power of two of at least
    /// `2^MIN_LOG_LEN`.
    pub fn new(mut entries: Vec<Entry>) -> Self {
        let log_len = (entries.len().next_power_of_two().trailing_zeros() as usize).max(MIN_LOG_LEN);
        entries.resize(1 << log_len, 0);
        let packed: Vec<F128> = entries.chunks(2).map(|p| F128::new(p[0], p[1])).collect();
        let params = pcs_params(log_len + 6);
        let (commitment, prover_data) = commit(&packed, &params);
        return Self {
            entries,
            log_len,
            packed,
            params,
            commitment,
            prover_data,
        };
    }

    /// The commitment a verifier pins.
    pub fn commitment(&self) -> &Commitment {
        return &self.commitment;
    }

    /// Entry-index bits.
    pub fn log_len(&self) -> usize {
        return self.log_len;
    }
}

/// What a verifier holds of a statement's entry list.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MatrixCommitment {
    /// Entry-index bits.
    pub log_len: usize,
    /// The commitment to the packed entries.
    pub commitment: Commitment,
}

impl MatrixKey {
    /// The verifier's part of the key.
    pub fn verifying(&self) -> MatrixCommitment {
        return MatrixCommitment {
            log_len: self.log_len,
            commitment: self.commitment.clone(),
        };
    }
}

/// A matrix proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MatrixProof {
    /// The claim batching's grinding nonce.
    pub mu_nonce: u64,
    /// Main sumcheck rounds: coefficients 0 and 2 to 8, and the grinding nonce.
    pub main: Vec<(Vec<F128>, u64)>,
    /// The counts of every lookup, concatenated.
    pub counts: Vec<F128>,
    /// The count points' grinding nonce.
    pub lookup_nonce: u64,
    /// Count sumcheck rounds: coefficients 0 and 2 to 15, and the grinding nonce.
    pub count: Vec<(Vec<F128>, u64)>,
    /// The address bits' extensions at the count sumcheck's point.
    pub bits: Vec<F128>,
    /// The skip point's grinding nonce.
    pub zeta_nonce: u64,
    /// The opening of the entry list.
    pub opening: BatchOpeningProofLigerito,
}

/// Why a matrix proof was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum MatrixError {
    /// A message has the wrong length.
    Shape,
    /// A grinding nonce is invalid.
    Grinding,
    /// The main sumcheck does not close.
    Main,
    /// The count sumcheck does not close.
    Count,
    /// The opening is refused.
    Opening,
}

/// A matrix claim's explicit-row part: its parameters and the value its entries must sum to.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExplicitClaim {
    /// The A-side challenge.
    pub alpha: F128,
    /// Row weights on the skipped variables.
    pub skip: Vec<F128>,
    /// The collapsed witness.
    pub z: Vec<F128>,
    /// The row point after the skip, LSB-first.
    pub x: Vec<F128>,
    /// The column point after the skip, LSB-first.
    pub r: Vec<F128>,
    /// The value.
    pub value: F128,
}

impl ExplicitClaim {
    /// The tables the claim reads the entries through.
    pub fn tables(&self) -> Tables {
        return Tables::new(self.alpha, &self.skip, &self.z, &self.x, &self.r);
    }
}

fn observe_claims<Ch: Challenger>(ch: &mut Ch, claims: &[ExplicitClaim]) {
    ch.observe_label(b"pofseed-flock-lift-committed-matrix");
    ch.observe_bytes(&(claims.len() as u64).to_le_bytes());
    for c in claims {
        ch.observe_f128(c.alpha);
        ch.observe_f128_slice(&c.skip);
        ch.observe_f128_slice(&c.z);
        ch.observe_f128_slice(&c.x);
        ch.observe_f128_slice(&c.r);
        ch.observe_f128(c.value);
    }
}

fn powers(x: F128, n: usize) -> Vec<F128> {
    return (0..n)
        .scan(F128::ONE, |p, _| {
            let v = *p;
            *p *= x;
            Some(v)
        })
        .collect();
}

/// Coefficients of `Π (a_i + b_i·X)`.
fn product(factors: impl Iterator<Item = (F128, F128)>, out: &mut Vec<F128>) {
    out.clear();
    out.push(F128::ONE);
    for (a, b) in factors {
        out.push(F128::ZERO);
        for d in (0..out.len()).rev() {
            let lower = if d > 0 { out[d - 1] } else { F128::ZERO };
            out[d] = out[d] * a + lower * b;
        }
    }
}

fn horner(coeffs: &[F128], x: F128) -> F128 {
    return coeffs.iter().rev().fold(F128::ZERO, |acc, &c| acc * x + c);
}

/// The full coefficients from a round message and the claim it must meet: `g(0) + g(1)` is the
/// sum of the coefficients from degree 1 up, so the degree-1 coefficient is implied.
fn expand(message: &[F128], claim: F128) -> Vec<F128> {
    let mut c = Vec::with_capacity(message.len() + 1);
    c.push(message[0]);
    let higher = message[1..].iter().fold(F128::ZERO, |a, &b| a + b);
    c.push(claim + higher);
    c.extend_from_slice(&message[1..]);
    return c;
}

fn compress(coeffs: &[F128]) -> Vec<F128> {
    let mut m = vec![coeffs[0]];
    m.extend_from_slice(&coeffs[2..]);
    return m;
}

/// Binds the lowest variable of every vector in `vs` to `r`.
fn bind(vs: &mut [Vec<F128>], r: F128) {
    vs.par_iter_mut().for_each(|v| {
        let half = v.len() / 2;
        for i in 0..half {
            let (e0, e1) = (v[2 * i], v[2 * i + 1]);
            v[i] = e0 + r * (e0 + e1);
        }
        v.truncate(half);
    });
}

/// Which part of a proof a forging prover adjusts so that the checks before it pass.
#[cfg(feature = "forgery")]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Forge {
    /// A count, so that the main sumcheck closes on wrong values.
    Counts,
    /// A count and an address bit, so that the count sumcheck closes as well.
    Bits,
}

/// Proves that every claim's value is the table-weighted sum of the key's entries under the
/// claim's tables.
pub fn prove<Ch: Challenger>(key: &MatrixKey, claims: &[ExplicitClaim], ch: &mut Ch) -> MatrixProof {
    return prove_inner(key, claims, None, ch);
}

/// Proves like [`prove`], but adjusts the part `forge` names so that every check before it passes
/// even when the claims' values are wrong.
#[cfg(feature = "forgery")]
pub fn prove_forged<Ch: Challenger>(key: &MatrixKey, claims: &[ExplicitClaim], forge: Forge, ch: &mut Ch) -> MatrixProof {
    return prove_inner(key, claims, Some(forge), ch);
}

#[cfg_attr(not(feature = "forgery"), allow(unused_variables, unused_mut))]
fn prove_inner<Ch: Challenger>(
    key: &MatrixKey,
    claims: &[ExplicitClaim],
    #[cfg(feature = "forgery")] forge: Option<Forge>,
    #[cfg(not(feature = "forgery"))] forge: Option<()>,
    ch: &mut Ch,
) -> MatrixProof {
    let n = key.log_len;
    observe_claims(ch, claims);
    let (mu_nonce, mu) = ch.grind_pow_and_sample_f128(MU_BITS);
    let weights = powers(mu, claims.len());
    let tables: Vec<Tables> = claims.iter().map(ExplicitClaim::tables).collect();
    let values: Vec<F128> = claims.iter().map(|c| c.value).collect();
    let mut e: Vec<Vec<F128>> = tables
        .iter()
        .flat_map(|t| (0..LOOKUPS).map(move |l| (t, l)))
        .collect::<Vec<_>>()
        .into_par_iter()
        .map(|(t, l)| key.entries.iter().map(|&x| t.tables[l][address(x, l)]).collect())
        .collect();
    let mut claim = values.iter().zip(&weights).fold(F128::ZERO, |a, (&v, &w)| a + v * w);
    let mut main = Vec::with_capacity(n);
    let mut rho = Vec::with_capacity(n);
    for _ in 0..n {
        let half = e[0].len() / 2;
        let coeffs = (0..half)
            .into_par_iter()
            .fold(
                || (vec![F128::ZERO; MAIN_DEGREE + 1], Vec::new()),
                |(mut acc, mut poly), i| {
                    for (c, &w) in weights.iter().enumerate() {
                        let f = &e[c * LOOKUPS..(c + 1) * LOOKUPS];
                        product(f.iter().map(|v| (v[2 * i], v[2 * i] + v[2 * i + 1])), &mut poly);
                        for (a, &p) in acc.iter_mut().zip(&poly) {
                            *a += w * p;
                        }
                    }
                    (acc, poly)
                },
            )
            .map(|(acc, _)| acc)
            .reduce(|| vec![F128::ZERO; MAIN_DEGREE + 1], |mut a, b| {
                a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
                a
            });
        let message = compress(&coeffs);
        ch.observe_f128_slice(&message);
        let (nonce, r) = ch.grind_pow_and_sample_f128(MAIN_BITS);
        claim = horner(&expand(&message, claim), r);
        main.push((message, nonce));
        rho.push(r);
        bind(&mut e, r);
    }
    drop(e);
    let eq_rho = build_eq_table(&rho);
    let mut counts = Vec::new();
    for l in 0..LOOKUPS {
        let mut c = vec![F128::ZERO; addresses(l)];
        for (k, &x) in key.entries.iter().enumerate() {
            c[address(x, l)] += eq_rho[k];
        }
        counts.extend(c);
    }
    #[cfg(feature = "forgery")]
    if forge.is_some() {
        let at = counts.len() - 1;
        let base = main_expected(&tables, &weights, &counts);
        counts[at] += F128::ONE;
        let slope = main_expected(&tables, &weights, &counts) + base;
        counts[at] += F128::ONE + (claim + base) * slope.inv();
    }
    ch.observe_f128_slice(&counts);
    let (lookup_nonce, gamma) = ch.grind_pow_and_sample_f128(LOOKUP_POINT_BITS);
    let points: Vec<Vec<F128>> = LOOKUP_BITS.iter().map(|&b| ch.sample_f128_vec(b)).collect();
    let gammas = powers(gamma, LOOKUPS);
    let mut claim = count_claim(&counts, &gammas, &points);
    let mut vs: Vec<Vec<F128>> = Vec::with_capacity(1 + ADDRESS_BITS);
    vs.push(eq_rho);
    for l in 0..LOOKUPS {
        for i in 0..LOOKUP_BITS[l] {
            let (r, pos) = (points[l][i], OFFSETS[l] + i);
            vs.push(key.entries.par_iter().map(|&x| if (x >> pos) & 1 == 1 { r } else { F128::ONE + r }).collect());
        }
    }
    let mut count = Vec::with_capacity(n);
    let mut sigma = Vec::with_capacity(n);
    for _ in 0..n {
        let half = vs[0].len() / 2;
        let coeffs = (0..half)
            .into_par_iter()
            .fold(
                || (vec![F128::ZERO; COUNT_DEGREE + 1], Vec::new(), Vec::new()),
                |(mut acc, mut poly, mut sum), i| {
                    sum.clear();
                    sum.resize(COUNT_DEGREE, F128::ZERO);
                    let mut at = 1;
                    for (l, &g) in gammas.iter().enumerate() {
                        let f = &vs[at..at + LOOKUP_BITS[l]];
                        at += LOOKUP_BITS[l];
                        product(f.iter().map(|v| (v[2 * i], v[2 * i] + v[2 * i + 1])), &mut poly);
                        for (s, &p) in sum.iter_mut().zip(&poly) {
                            *s += g * p;
                        }
                    }
                    let (a, b) = (vs[0][2 * i], vs[0][2 * i] + vs[0][2 * i + 1]);
                    for d in 0..COUNT_DEGREE {
                        acc[d] += a * sum[d];
                        acc[d + 1] += b * sum[d];
                    }
                    (acc, poly, sum)
                },
            )
            .map(|(acc, _, _)| acc)
            .reduce(|| vec![F128::ZERO; COUNT_DEGREE + 1], |mut a, b| {
                a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
                a
            });
        let message = compress(&coeffs);
        ch.observe_f128_slice(&message);
        let (nonce, r) = ch.grind_pow_and_sample_f128(COUNT_BITS);
        claim = horner(&expand(&message, claim), r);
        count.push((message, nonce));
        sigma.push(r);
        bind(&mut vs, r);
    }
    drop(vs);
    let eq_sigma = build_eq_table(&sigma);
    let mut bits = vec![F128::ZERO; ADDRESS_BITS];
    for (pos, b) in bits.iter_mut().enumerate() {
        *b = key
            .entries
            .par_iter()
            .zip(eq_sigma.par_iter())
            .filter(|(x, _)| (**x >> pos) & 1 == 1)
            .map(|(_, &w)| w)
            .reduce(|| F128::ZERO, |a, b| a + b);
    }
    #[cfg(feature = "forgery")]
    if forge == Some(Forge::Bits) {
        let eq = rho.iter().zip(&sigma).fold(F128::ONE, |a, (&x, &y)| a * (F128::ONE + x + y));
        let at = OFFSETS[LOOKUPS - 1];
        let base = eq * count_sum(&gammas, &points, &bits);
        bits[at] += F128::ONE;
        let slope = eq * count_sum(&gammas, &points, &bits) + base;
        bits[at] += F128::ONE + (claim + base) * slope.inv();
    }
    ch.observe_f128_slice(&bits);
    let (zeta_nonce, _zeta) = ch.grind_pow_and_sample_f128(ZETA_BITS);
    let lig_config = key.params.ligerito_prover_config().expect("registered Ligerito configuration");
    let opening = open_batch_mixed_ligerito_with_precomputed_s_hat_v_and_grinding(
        key.packed.clone(),
        &key.prover_data,
        &key.commitment,
        &[sigma.as_slice()],
        &[None],
        &[],
        &PaddingSpec::dense(key.params.m),
        &lig_config,
        key.params.opening_grinding(),
        ch,
    );
    return MatrixProof {
        mu_nonce,
        main,
        counts,
        lookup_nonce,
        count,
        bits,
        zeta_nonce,
        opening,
    };
}

/// `Σ_c w_c·Π_l Σ_a T_{c,l}[a]·ĉ_l[a]`.
fn main_expected(tables: &[Tables], weights: &[F128], counts: &[F128]) -> F128 {
    let mut expected = F128::ZERO;
    for (t, &w) in tables.iter().zip(weights) {
        let mut term = w;
        let mut at = 0;
        for l in 0..LOOKUPS {
            let c = &counts[at..at + addresses(l)];
            at += addresses(l);
            term *= c.iter().zip(&t.tables[l]).fold(F128::ZERO, |a, (&x, &y)| a + x * y);
        }
        expected += term;
    }
    return expected;
}

/// `Σ_l γ^l·Π_i (1 + r_{l,i} + b_{l,i})`.
fn count_sum(gammas: &[F128], points: &[Vec<F128>], bits: &[F128]) -> F128 {
    let mut sum = F128::ZERO;
    for l in 0..LOOKUPS {
        let mut prod = gammas[l];
        for i in 0..LOOKUP_BITS[l] {
            prod *= F128::ONE + points[l][i] + bits[OFFSETS[l] + i];
        }
        sum += prod;
    }
    return sum;
}

/// `Σ_l γ^l·Σ_a eq(r_l, a)·ĉ_l[a]`.
fn count_claim(counts: &[F128], gammas: &[F128], points: &[Vec<F128>]) -> F128 {
    let mut at = 0;
    let mut acc = F128::ZERO;
    for l in 0..LOOKUPS {
        let eq = build_eq_table(&points[l]);
        let c = &counts[at..at + addresses(l)];
        at += addresses(l);
        acc += gammas[l] * c.iter().zip(&eq).fold(F128::ZERO, |a, (&x, &y)| a + x * y);
    }
    return acc;
}

/// Verifies that every claim's value is the table-weighted sum of the committed entries under
/// the claim's tables.
pub fn verify<Ch: Challenger>(
    key: &MatrixCommitment,
    claims: &[ExplicitClaim],
    proof: &MatrixProof,
    ch: &mut Ch,
) -> Result<(), MatrixError> {
    let n = key.log_len;
    let total: usize = (0..LOOKUPS).map(addresses).sum();
    if claims.is_empty()
        || proof.main.len() != n
        || proof.count.len() != n
        || proof.counts.len() != total
        || proof.bits.len() != ADDRESS_BITS
        || proof.main.iter().any(|(m, _)| m.len() != MAIN_DEGREE)
        || proof.count.iter().any(|(m, _)| m.len() != COUNT_DEGREE)
    {
        return Err(MatrixError::Shape);
    }
    observe_claims(ch, claims);
    let mu = ch.verify_pow_and_sample_f128(proof.mu_nonce, MU_BITS).ok_or(MatrixError::Grinding)?;
    let weights = powers(mu, claims.len());
    let mut claim = claims.iter().zip(&weights).fold(F128::ZERO, |a, (c, &w)| a + c.value * w);
    let mut rho = Vec::with_capacity(n);
    for (message, nonce) in &proof.main {
        let coeffs = expand(message, claim);
        ch.observe_f128_slice(message);
        let r = ch.verify_pow_and_sample_f128(*nonce, MAIN_BITS).ok_or(MatrixError::Grinding)?;
        claim = horner(&coeffs, r);
        rho.push(r);
    }
    let tables: Vec<Tables> = claims.iter().map(ExplicitClaim::tables).collect();
    if main_expected(&tables, &weights, &proof.counts) != claim {
        return Err(MatrixError::Main);
    }
    ch.observe_f128_slice(&proof.counts);
    let gamma = ch
        .verify_pow_and_sample_f128(proof.lookup_nonce, LOOKUP_POINT_BITS)
        .ok_or(MatrixError::Grinding)?;
    let points: Vec<Vec<F128>> = LOOKUP_BITS.iter().map(|&b| ch.sample_f128_vec(b)).collect();
    let gammas = powers(gamma, LOOKUPS);
    let mut claim = count_claim(&proof.counts, &gammas, &points);
    let mut sigma = Vec::with_capacity(n);
    for (message, nonce) in &proof.count {
        let coeffs = expand(message, claim);
        ch.observe_f128_slice(message);
        let r = ch.verify_pow_and_sample_f128(*nonce, COUNT_BITS).ok_or(MatrixError::Grinding)?;
        claim = horner(&coeffs, r);
        sigma.push(r);
    }
    let eq = rho.iter().zip(&sigma).fold(F128::ONE, |a, (&x, &y)| a * (F128::ONE + x + y));
    if eq * count_sum(&gammas, &points, &proof.bits) != claim {
        return Err(MatrixError::Count);
    }
    ch.observe_f128_slice(&proof.bits);
    let zeta = ch.verify_pow_and_sample_f128(proof.zeta_nonce, ZETA_BITS).ok_or(MatrixError::Grinding)?;
    let z_skip = SkipPoint::Phi8(zeta);
    let value = z_skip.weights(6).iter().zip(&proof.bits).fold(F128::ZERO, |a, (&w, &b)| a + w * b);
    let opened = ZClaim {
        point: QuirkyPoint {
            z_skip,
            x_inner_rest: sigma,
            x_outer: Vec::new(),
        },
        value,
    };
    return verify_claims_ligerito(&key.commitment, &[opened], &proof.opening, &pcs_params(n + 6), ch)
        .map_err(|_| MatrixError::Opening);
}
