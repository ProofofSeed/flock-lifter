// SPDX-License-Identifier: LGPL-3.0-or-later
//! The WHIR polynomial commitment: commitment, opening at points, and verification.

use crate::domain::Domain;
use crate::field::{
    bytes_f128, bytes_f256, eq_eval, eq_table, fold, fold_base, mle_eval, mle_eval_base,
    shift_eval, shift_table,
};
use crate::merkle::{self, Tree};
use crate::params::{Config, ConfigError, Round, Schedule};
use flock_prover::challenger::Challenger;
use flock_prover::field::{F128, F256};
use flock_prover::merkle::Hash;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A commitment: the cap of the codeword's Merkle tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Commitment {
    /// The cap of the codeword's tree.
    pub cap: Vec<Hash>,
}

/// What the prover keeps of a commitment.
pub struct Committed {
    config: Config,
    schedule: Schedule,
    message: Vec<F128>,
    tree: Tree,
    codeword: Vec<F128>,
    cap: Vec<Hash>,
}

/// Opened codeword rows and their paths.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Openings {
    /// Rows of the initial codeword, over GF(2^128).
    Base(Vec<F128>, Vec<Vec<Hash>>),
    /// Rows of a later codeword, over GF(2^256).
    Ext(Vec<F256>, Vec<Vec<Hash>>),
}

/// One folded function: its cap, its out-of-domain answers, the grinding nonce before the previous
/// function's queries, and those queries' openings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundProof {
    /// The cap of the folded function's tree.
    pub cap: Vec<Hash>,
    /// The folded function at out-of-domain points.
    pub ood: Vec<F256>,
    /// The proof-of-work nonce.
    pub pow: u64,
    /// The previous function's opened rows.
    pub openings: Openings,
}

/// An opening proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proof {
    /// The committed polynomial at out-of-domain points.
    pub ood: Vec<F256>,
    /// Every sumcheck round's `h(1)` and leading coefficient, in order.
    pub sumcheck: Vec<[F256; 2]>,
    /// The folded functions.
    pub rounds: Vec<RoundProof>,
    /// The final polynomial's values over the hypercube.
    pub final_poly: Vec<F256>,
    /// The proof-of-work nonce before the final queries.
    pub final_pow: u64,
    /// The last committed function's opened rows.
    pub final_openings: Openings,
}

impl Proof {
    /// The serialised proof.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialisable")
    }
}

/// Why an opening was refused.
#[derive(Clone, Debug, PartialEq)]
pub enum VerifyError {
    /// The configuration is refused.
    Config(ConfigError),
    /// A part of the proof or commitment has the wrong length.
    Shape,
    /// A proof-of-work nonce is invalid, in the given round.
    Pow(usize),
    /// An opened row is not under its cap, in the given round.
    Merkle(usize),
    /// The final polynomial disagrees with an opened row.
    Final,
    /// The last sumcheck claim does not hold.
    Sumcheck,
}

/// A weight over the committed polynomial's hypercube, known in full to the prover and at single
/// points to the verifier.
pub trait Weight: Sync {
    /// The weight's values over the hypercube.
    fn table(&self) -> Vec<F256>;
    /// The weight's multilinear extension at `point`.
    fn eval(&self, point: &[F256]) -> F256;
}

/// A constraint the running weight gained: its coefficient, the variables it spans, and its kind.
enum Term<'a> {
    Eq(F256, Vec<F256>),
    Shift(F256, Vec<F128>),
    Weight(F256, &'a dyn Weight),
}

impl Term<'_> {
    fn eval(&self, point: &[F256]) -> F256 {
        match self {
            Term::Eq(c, z) => *c * eq_eval(z, &point[point.len() - z.len()..]),
            Term::Shift(c, w) => *c * shift_eval(w, &point[point.len() - w.len()..]),
            Term::Weight(c, w) => *c * w.eval(point),
        }
    }
}

fn start<Ch: Challenger + ?Sized>(config: &Config, cap: &[Hash], ch: &mut Ch) {
    ch.observe_label(b"flock-whir-v1");
    ch.observe_bytes(&config.to_bytes());
    ch.observe_bytes(cap.as_flattened());
}

fn sample_point<Ch: Challenger + ?Sized>(vars: usize, ch: &mut Ch) -> Vec<F256> {
    (0..vars).map(|_| ch.sample_f256()).collect()
}

fn positions(words: &[F128], log_domain: usize) -> Vec<usize> {
    words.iter().map(|w| (w.lo as usize) & ((1 << log_domain) - 1)).collect()
}

fn powers(g: F256, n: usize) -> Vec<F256> {
    let mut out = Vec::with_capacity(n);
    let mut p = g;
    for _ in 0..n {
        out.push(p);
        p *= g;
    }
    out
}

/// Advances a sumcheck claim past a round message at challenge `r`.
fn next_claim(claim: F256, msg: [F256; 2], r: F256) -> F256 {
    let [e1, einf] = msg;
    let a = claim + e1;
    let b = claim + einf;
    a + (b + einf * r) * r
}

/// Runs `rounds` sumcheck rounds of `Σ f·w` over dense vectors, folding both.
fn sumcheck_dense<Ch: Challenger + ?Sized>(
    f: &mut Vec<F256>,
    w: &mut Vec<F256>,
    rounds: usize,
    claim: &mut F256,
    msgs: &mut Vec<[F256; 2]>,
    ch: &mut Ch,
) -> Vec<F256> {
    let mut alphas = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let (e1, einf) = f
            .par_chunks(2)
            .zip(w.par_chunks(2))
            .map(|(a, b)| (a[1] * b[1], (a[0] + a[1]) * (b[0] + b[1])))
            .reduce(|| (F256::ZERO, F256::ZERO), |x, y| (x.0 + y.0, x.1 + y.1));
        ch.observe_f256(e1);
        ch.observe_f256(einf);
        let r = ch.sample_f256();
        *claim = next_claim(*claim, [e1, einf], r);
        msgs.push([e1, einf]);
        *f = fold(f, r);
        *w = fold(w, r);
        alphas.push(r);
    }
    alphas
}

fn ood_answers(message: &[F128], points: &[Vec<F256>]) -> Vec<F256> {
    points.iter().map(|z| mle_eval_base(message, z)).collect()
}

/// Commits to the multilinear polynomial with hypercube values `message`.
pub fn commit(config: &Config, message: Vec<F128>) -> Result<(Commitment, Committed), ConfigError> {
    let schedule = config.schedule()?;
    assert_eq!(message.len(), 1 << config.num_vars);
    let r0 = schedule.rounds[0];
    let domain = Domain::new(r0.log_domain);
    let lanes = 1 << r0.fold;
    let codeword = domain.encode(&message, lanes);
    let tree = Tree::new(bytes_f128(&codeword), domain.size(), r0.queries, config.merkle);
    let cap = tree.cap();
    Ok((
        Commitment { cap: cap.clone() },
        Committed { config: *config, schedule, message, tree, codeword, cap },
    ))
}

fn bind_claims<Ch: Challenger + ?Sized>(
    points: &[Vec<F256>],
    values: &[F256],
    weighted: &[F256],
    ch: &mut Ch,
) {
    ch.observe_label(b"flock-whir-open");
    ch.observe_bytes(&[points.len() as u64, weighted.len() as u64].map(u64::to_le_bytes).concat());
    for (z, &v) in points.iter().zip(values) {
        z.iter().for_each(|&c| ch.observe_f256(c));
        ch.observe_f256(v);
    }
    weighted.iter().for_each(|&v| ch.observe_f256(v));
}

fn phase(label: &str) {
    thread_local! {
        static LAST: std::cell::Cell<Option<std::time::Instant>> = const { std::cell::Cell::new(None) };
    }
    if std::env::var_os("WHIR_TIMING").is_none() {
        return;
    }
    let now = std::time::Instant::now();
    if let Some(last) = LAST.with(|l| l.replace(Some(now))) {
        eprintln!("[whir] {label}: {:.1} ms", (now - last).as_secs_f64() * 1e3);
    }
}

/// Opens a commitment at `points`, returning the values there and the proof.
pub fn open<Ch: Challenger + ?Sized>(
    committed: Committed,
    points: &[Vec<F256>],
    ch: &mut Ch,
) -> (Vec<F256>, Proof) {
    let (values, _, proof) = open_weighted(committed, points, &[], ch);
    (values, proof)
}

/// Opens a commitment at `points` and against `weights`, returning the values at the points, the
/// weighted sums and the proof.
pub fn open_weighted<Ch: Challenger + ?Sized>(
    committed: Committed,
    points: &[Vec<F256>],
    weights: &[&dyn Weight],
    ch: &mut Ch,
) -> (Vec<F256>, Vec<F256>, Proof) {
    let Committed { config, schedule, message, tree, codeword, cap } = committed;
    let rounds = &schedule.rounds;
    phase("start");
    start(&config, &cap, ch);
    let ood_points: Vec<Vec<F256>> =
        (0..rounds[0].ood).map(|_| sample_point(config.num_vars, ch)).collect();
    let ood_values = ood_answers(&message, &ood_points);
    ood_values.iter().for_each(|&v| ch.observe_f256(v));
    let values: Vec<F256> = points.iter().map(|z| mle_eval_base(&message, z)).collect();
    let weight_tables: Vec<Vec<F256>> = weights.iter().map(|w| w.table()).collect();
    assert!(
        weight_tables.iter().all(|t| t.len() == message.len()),
        "a weight spans every variable"
    );
    let weighted: Vec<F256> = weight_tables
        .iter()
        .map(|t| {
            t.par_iter()
                .zip(message.par_iter())
                .map(|(&w, &v)| w * v)
                .reduce(|| F256::ZERO, |a, b| a + b)
        })
        .collect();
    bind_claims(points, &values, &weighted, ch);
    let all_points: Vec<Vec<F256>> = ood_points.iter().chain(points).cloned().collect();
    let all_values: Vec<F256> =
        ood_values.iter().chain(&values).chain(&weighted).copied().collect();
    let gamma = powers(ch.sample_f256(), all_values.len());
    let mut claim = all_values.iter().zip(&gamma).fold(F256::ZERO, |acc, (&v, &g)| acc + g * v);
    let (gamma, weight_gamma) = gamma.split_at(all_points.len());
    let mut dense = combine(&weight_tables, weight_gamma);
    let mut dense_f: Vec<F256> = Vec::new();
    let mut msgs = Vec::new();
    let k0 = rounds[0].fold;
    let lanes = 1usize << k0;
    let eq_hi: Vec<Vec<F256>> = all_points.iter().map(|z| eq_table(&z[k0..])).collect();
    let mut tables: Vec<(Vec<F256>, Vec<F256>)> = all_points
        .iter()
        .zip(&eq_hi)
        .zip(gamma)
        .map(|((z, hi), &g)| {
            let a = message
                .par_chunks(lanes)
                .zip(hi.par_iter())
                .fold(
                    || vec![F256::ZERO; lanes],
                    |mut acc, (row, &e)| {
                        acc.iter_mut().zip(row).for_each(|(s, &v)| *s += e * v);
                        acc
                    },
                )
                .reduce(
                    || vec![F256::ZERO; lanes],
                    |mut x, y| {
                        x.iter_mut().zip(y).for_each(|(s, v)| *s += v);
                        x
                    },
                );
            let lo: Vec<F256> = eq_table(&z[..k0]).into_iter().map(|e| e * g).collect();
            (a, lo)
        })
        .collect();
    phase("round 0 tables");
    let mut alpha = Vec::with_capacity(k0);
    for j in 0..k0 {
        let (mut e1, mut einf) = tables.iter().fold((F256::ZERO, F256::ZERO), |acc, (a, e)| {
            a.chunks(2)
                .zip(e.chunks(2))
                .fold(acc, |(x, y), (p, q)| (x + p[1] * q[1], y + (p[0] + p[1]) * (q[0] + q[1])))
        });
        if let Some(w) = &dense {
            let (d1, dinf) = if j == 0 {
                message
                    .par_chunks(2)
                    .zip(w.par_chunks(2))
                    .map(|(a, b)| (b[1] * a[1], (b[0] + b[1]) * (a[0] + a[1])))
                    .reduce(|| (F256::ZERO, F256::ZERO), |x, y| (x.0 + y.0, x.1 + y.1))
            } else {
                dense_f
                    .par_chunks(2)
                    .zip(w.par_chunks(2))
                    .map(|(a, b)| (a[1] * b[1], (a[0] + a[1]) * (b[0] + b[1])))
                    .reduce(|| (F256::ZERO, F256::ZERO), |x, y| (x.0 + y.0, x.1 + y.1))
            };
            e1 += d1;
            einf += dinf;
        }
        ch.observe_f256(e1);
        ch.observe_f256(einf);
        let r = ch.sample_f256();
        claim = next_claim(claim, [e1, einf], r);
        msgs.push([e1, einf]);
        for (a, e) in tables.iter_mut() {
            *a = fold(a, r);
            *e = fold(e, r);
        }
        if let Some(w) = &mut dense {
            dense_f = if j == 0 { fold_base(&message, r) } else { fold(&dense_f, r) };
            *w = fold(w, r);
        }
        alpha.push(r);
    }
    phase("round 0 sumcheck");
    let eq_alpha = eq_table(&alpha);
    let mut g: Vec<F256> = message
        .par_chunks(lanes)
        .map(|row| row.iter().zip(&eq_alpha).fold(F256::ZERO, |acc, (&v, &e)| acc + e * v))
        .collect();
    let scale: Vec<F256> = tables.iter().map(|(_, e)| e[0]).collect();
    let mut w: Vec<F256> = (0..g.len())
        .into_par_iter()
        .map(|h| eq_hi.iter().zip(&scale).fold(F256::ZERO, |acc, (t, &s)| acc + s * t[h]))
        .collect();
    if let Some(d) = dense {
        add_scaled(&mut w, &d, F256::ONE);
    }
    let mut prev = Prev::Base { codeword, tree, round: rounds[0], alpha };
    let mut proofs = Vec::with_capacity(rounds.len() - 1);
    phase("round 0 fold and weights");
    for round in &rounds[1..] {
        let domain = Domain::new(round.log_domain);
        let word = domain.encode_f256(&g, 1 << round.fold);
        let tree = Tree::new(bytes_f256(&word), domain.size(), round.queries, config.merkle);
        let cap = tree.cap();
        ch.observe_bytes(cap.as_flattened());
        let ood_points: Vec<Vec<F256>> =
            (0..round.ood).map(|_| sample_point(round.vars, ch)).collect();
        let ood: Vec<F256> = ood_points.iter().map(|z| mle_eval(&g, z)).collect();
        ood.iter().for_each(|&v| ch.observe_f256(v));
        phase("encode, commit, out-of-domain");
        let (pow, words) = ch.grind_pow_and_sample_f128_vec(config.pow_bits, prev.round().queries);
        let (positions, openings, shifts) = prev.query(round.vars, &words);
        phase("grind and open");
        let gamma = powers(ch.sample_f256(), ood.len() + positions.len());
        let (ood_gamma, shift_gamma) = gamma.split_at(ood.len());
        for ((z, &y), &c) in ood_points.iter().zip(&ood).zip(ood_gamma) {
            claim += c * y;
            add_scaled(&mut w, &eq_table(z), c);
        }
        for (&y, &c) in prev.fold_values(&positions).iter().zip(shift_gamma) {
            claim += c * y;
        }
        add_shift_terms(&mut w, &shifts, shift_gamma);
        phase("weights");
        let alpha = sumcheck_dense(&mut g, &mut w, round.fold, &mut claim, &mut msgs, ch);
        phase("sumcheck");
        proofs.push(RoundProof { cap, ood, pow, openings });
        prev = Prev::Ext { codeword: word, tree, round: *round, alpha };
    }
    g.iter().for_each(|&v| ch.observe_f256(v));
    let final_poly = g.clone();
    phase("rounds done");
    let (final_pow, words) =
        ch.grind_pow_and_sample_f128_vec(config.pow_bits, prev.round().queries);
    let (_, final_openings, _) = prev.query(schedule.final_vars, &words);
    sumcheck_dense(&mut g, &mut w, schedule.final_vars, &mut claim, &mut msgs, ch);
    debug_assert_eq!(claim, g[0] * w[0]);
    (
        values,
        weighted,
        Proof {
            ood: ood_values,
            sumcheck: msgs,
            rounds: proofs,
            final_poly,
            final_pow,
            final_openings,
        },
    )
}

/// The combination `Σ_j c_j·t_j` of weight tables, if there are any.
fn combine(tables: &[Vec<F256>], c: &[F256]) -> Option<Vec<F256>> {
    let (first, rest) = tables.split_first()?;
    let mut out: Vec<F256> = first.par_iter().map(|&v| c[0] * v).collect();
    for (t, &g) in rest.iter().zip(&c[1..]) {
        add_scaled(&mut out, t, g);
    }
    Some(out)
}

fn add_scaled(w: &mut [F256], t: &[F256], c: F256) {
    w.par_iter_mut().zip(t.par_iter()).for_each(|(a, &b)| *a += c * b);
}

/// Adds `Σ_j c_j·T_j` to `w`, `T_j` the shift weight of `coords[j]`, each split into a low and a
/// high factor so that the sum is one small matrix product rather than a pass per term.
fn add_shift_terms(w: &mut [F256], coords: &[Vec<F128>], c: &[F256]) {
    if coords.is_empty() {
        return;
    }
    let vars = coords[0].len();
    let low = vars / 2;
    let lo: Vec<Vec<F256>> = coords
        .par_iter()
        .zip(c)
        .map(|(x, &g)| shift_table(&x[..low]).into_iter().map(|v| g * v).collect())
        .collect();
    let hi: Vec<Vec<F128>> = coords.par_iter().map(|x| shift_table(&x[low..])).collect();
    w.par_chunks_mut(1 << low).enumerate().for_each(|(h, row)| {
        for (l, f) in lo.iter().zip(&hi) {
            let s = f[h];
            row.iter_mut().zip(l).for_each(|(a, &b)| *a += b * s);
        }
    });
}

/// The previous committed function, whose rows the next round queries.
enum Prev {
    Base { codeword: Vec<F128>, tree: Tree, round: Round, alpha: Vec<F256> },
    Ext { codeword: Vec<F256>, tree: Tree, round: Round, alpha: Vec<F256> },
}

impl Prev {
    fn round(&self) -> Round {
        match self {
            Prev::Base { round, .. } | Prev::Ext { round, .. } => *round,
        }
    }

    /// Opens the query positions the sampled `words` select, returning the positions, the
    /// openings and each position's coordinates over `vars` variables.
    fn query(&self, vars: usize, words: &[F128]) -> (Vec<usize>, Openings, Vec<Vec<F128>>) {
        let round = self.round();
        let positions = positions(words, round.log_domain);
        let lanes = 1 << round.fold;
        let domain = Domain::new(round.log_domain);
        let coords = positions.iter().map(|&p| domain.coordinates(p, vars)).collect();
        let openings = match self {
            Prev::Base { codeword, tree, .. } => Openings::Base(
                positions
                    .iter()
                    .flat_map(|&p| codeword[p * lanes..(p + 1) * lanes].iter().copied())
                    .collect(),
                positions.iter().map(|&p| tree.path(p)).collect(),
            ),
            Prev::Ext { codeword, tree, .. } => Openings::Ext(
                positions
                    .iter()
                    .flat_map(|&p| codeword[p * lanes..(p + 1) * lanes].iter().copied())
                    .collect(),
                positions.iter().map(|&p| tree.path(p)).collect(),
            ),
        };
        (positions, openings, coords)
    }

    /// The folded function's values at `positions`.
    fn fold_values(&self, positions: &[usize]) -> Vec<F256> {
        let round = self.round();
        let lanes = 1 << round.fold;
        match self {
            Prev::Base { codeword, alpha, .. } => {
                let eq = eq_table(alpha);
                positions
                    .iter()
                    .map(|&p| {
                        codeword[p * lanes..(p + 1) * lanes]
                            .iter()
                            .zip(&eq)
                            .fold(F256::ZERO, |a, (&v, &e)| a + e * v)
                    })
                    .collect()
            }
            Prev::Ext { codeword, alpha, .. } => {
                let eq = eq_table(alpha);
                positions
                    .iter()
                    .map(|&p| {
                        codeword[p * lanes..(p + 1) * lanes]
                            .iter()
                            .zip(&eq)
                            .fold(F256::ZERO, |a, (&v, &e)| a + e * v)
                    })
                    .collect()
            }
        }
    }
}

/// Verifies that the committed polynomial takes `values` at `points`.
pub fn verify<Ch: Challenger + ?Sized>(
    config: &Config,
    commitment: &Commitment,
    points: &[Vec<F256>],
    values: &[F256],
    proof: &Proof,
    ch: &mut Ch,
) -> Result<(), VerifyError> {
    verify_weighted(config, commitment, points, values, &[], &[], proof, ch)
}

/// Verifies that the committed polynomial takes `values` at `points` and has the sums `weighted`
/// against `weights`.
pub fn verify_weighted<Ch: Challenger + ?Sized>(
    config: &Config,
    commitment: &Commitment,
    points: &[Vec<F256>],
    values: &[F256],
    weights: &[&dyn Weight],
    weighted: &[F256],
    proof: &Proof,
    ch: &mut Ch,
) -> Result<(), VerifyError> {
    let schedule = config.schedule().map_err(VerifyError::Config)?;
    let rounds = &schedule.rounds;
    let m = config.num_vars;
    let total_sumcheck = m;
    if points.len() != values.len()
        || weights.len() != weighted.len()
        || points.iter().any(|z| z.len() != m)
        || proof.sumcheck.len() != total_sumcheck
        || proof.rounds.len() != rounds.len() - 1
        || proof.final_poly.len() != 1 << schedule.final_vars
    {
        return Err(VerifyError::Shape);
    }
    let r0 = rounds[0];
    if commitment.cap.len() != merkle::cap_size(1 << r0.log_domain, r0.queries)
        || proof.ood.len() != r0.ood
    {
        return Err(VerifyError::Shape);
    }
    start(config, &commitment.cap, ch);
    let ood_points: Vec<Vec<F256>> = (0..r0.ood).map(|_| sample_point(m, ch)).collect();
    proof.ood.iter().for_each(|&v| ch.observe_f256(v));
    bind_claims(points, values, weighted, ch);
    let all_points: Vec<Vec<F256>> = ood_points.iter().chain(points).cloned().collect();
    let all_values: Vec<F256> = proof.ood.iter().chain(values).chain(weighted).copied().collect();
    let gamma = powers(ch.sample_f256(), all_values.len());
    let mut claim = all_values.iter().zip(&gamma).fold(F256::ZERO, |acc, (&v, &g)| acc + g * v);
    let (gamma, weight_gamma) = gamma.split_at(all_points.len());
    let mut terms: Vec<Term> =
        all_points.iter().zip(gamma).map(|(z, &g)| Term::Eq(g, z.clone())).collect();
    terms.extend(weights.iter().zip(weight_gamma).map(|(&w, &g)| Term::Weight(g, w)));
    let mut msgs = proof.sumcheck.iter();
    let mut challenges: Vec<F256> = Vec::with_capacity(m);
    let mut run =
        |n: usize, claim: &mut F256, challenges: &mut Vec<F256>, ch: &mut Ch| -> Vec<F256> {
            let mut alpha = Vec::with_capacity(n);
            for _ in 0..n {
                let msg = *msgs.next().expect("length checked");
                ch.observe_f256(msg[0]);
                ch.observe_f256(msg[1]);
                let r = ch.sample_f256();
                *claim = next_claim(*claim, msg, r);
                alpha.push(r);
            }
            challenges.extend_from_slice(&alpha);
            alpha
        };
    let mut alpha = run(rounds[0].fold, &mut claim, &mut challenges, ch);
    let mut prev_cap = commitment.cap.clone();
    let mut prev_round = rounds[0];
    for (i, (round, rp)) in rounds[1..].iter().zip(&proof.rounds).enumerate() {
        if rp.cap.len() != merkle::cap_size(1 << round.log_domain, round.queries)
            || rp.ood.len() != round.ood
        {
            return Err(VerifyError::Shape);
        }
        ch.observe_bytes(rp.cap.as_flattened());
        let ood_points: Vec<Vec<F256>> =
            (0..round.ood).map(|_| sample_point(round.vars, ch)).collect();
        rp.ood.iter().for_each(|&v| ch.observe_f256(v));
        let words = ch
            .verify_pow_and_sample_f128_vec(rp.pow, config.pow_bits, prev_round.queries)
            .ok_or(VerifyError::Pow(i + 1))?;
        let folded =
            check_openings(config, &prev_cap, &prev_round, &alpha, &rp.openings, round.vars, i, &words)?;
        let gamma = powers(ch.sample_f256(), rp.ood.len() + folded.len());
        let (ood_gamma, shift_gamma) = gamma.split_at(rp.ood.len());
        for ((z, &y), &c) in ood_points.into_iter().zip(&rp.ood).zip(ood_gamma) {
            claim += c * y;
            terms.push(Term::Eq(c, z));
        }
        for ((coords, y), &c) in folded.into_iter().zip(shift_gamma) {
            claim += c * y;
            terms.push(Term::Shift(c, coords));
        }
        alpha = run(round.fold, &mut claim, &mut challenges, ch);
        prev_cap = rp.cap.clone();
        prev_round = *round;
    }
    proof.final_poly.iter().for_each(|&v| ch.observe_f256(v));
    let words = ch
        .verify_pow_and_sample_f128_vec(proof.final_pow, config.pow_bits, prev_round.queries)
        .ok_or(VerifyError::Pow(rounds.len()))?;
    let folded = check_openings(
        config,
        &prev_cap,
        &prev_round,
        &alpha,
        &proof.final_openings,
        schedule.final_vars,
        rounds.len() - 1,
        &words,
    )?;
    for (coords, y) in folded {
        let table = shift_table(&coords);
        let value = proof.final_poly.iter().zip(&table).fold(F256::ZERO, |a, (&v, &t)| a + v * t);
        if value != y {
            return Err(VerifyError::Final);
        }
    }
    let r = run(schedule.final_vars, &mut claim, &mut challenges, ch);
    let weight = terms.iter().fold(F256::ZERO, |acc, t| acc + t.eval(&challenges));
    if claim != mle_eval(&proof.final_poly, &r) * weight {
        return Err(VerifyError::Sumcheck);
    }
    Ok(())
}

/// Checks a committed function's opened rows at the positions the sampled `words` select against
/// its cap, and returns each position's coordinates with the folded function's value there.
fn check_openings(
    config: &Config,
    cap: &[Hash],
    round: &Round,
    alpha: &[F256],
    openings: &Openings,
    vars: usize,
    index: usize,
    words: &[F128],
) -> Result<Vec<(Vec<F128>, F256)>, VerifyError> {
    let positions = positions(words, round.log_domain);
    let lanes = 1 << round.fold;
    let leaves = 1 << round.log_domain;
    let eq = eq_table(alpha);
    let domain = Domain::new(round.log_domain);
    let mut out = Vec::with_capacity(positions.len());
    let (count, paths) = match openings {
        Openings::Base(rows, paths) => (rows.len(), paths),
        Openings::Ext(rows, paths) => (rows.len(), paths),
    };
    if count != positions.len() * lanes
        || paths.len() != positions.len()
        || matches!(openings, Openings::Base(..)) != (index == 0)
    {
        return Err(VerifyError::Shape);
    }
    for (q, &p) in positions.iter().enumerate() {
        let (leaf, value) = match openings {
            Openings::Base(rows, _) => {
                let row = &rows[q * lanes..(q + 1) * lanes];
                (
                    bytes_f128(row).to_vec(),
                    row.iter().zip(&eq).fold(F256::ZERO, |a, (&v, &e)| a + e * v),
                )
            }
            Openings::Ext(rows, _) => {
                let row = &rows[q * lanes..(q + 1) * lanes];
                (
                    bytes_f256(row).to_vec(),
                    row.iter().zip(&eq).fold(F256::ZERO, |a, (&v, &e)| a + e * v),
                )
            }
        };
        if !merkle::verify(cap, leaves, &leaf, p, &paths[q], config.merkle) {
            return Err(VerifyError::Merkle(index));
        }
        out.push((domain.coordinates(p, vars), value));
    }
    Ok(out)
}
