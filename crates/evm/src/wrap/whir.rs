// SPDX-License-Identifier: LGPL-3.0-or-later

//! The WHIR opening as the contract verifies it, reading the calldata encoding: codeword rows on
//! Keccak-256 trees, the folds' sumcheck, and the final weight in closed form.

use flock_prover::{
    challenger::Challenger,
    field::{F128, F256},
};
use pofseed_flock_lift::transcript::KeccakChallenger;
use pofseed_flock_lift_whir::{
    domain::Domain,
    merkle::{cap_size, keccak_leaf, keccak_node},
    params::{Config, Round},
    whir::{Openings, Proof},
};

use crate::{
    calldata::Writer,
    mirror::{Reader, Reject, Result, pow_vec},
};

fn f256_row(w: &mut Writer, v: F256) {
    w.f128(v.c0);
    w.f128(v.c1);
}

fn openings(w: &mut Writer, o: &Openings) {
    let paths = match o {
        Openings::Base(rows, paths) => {
            rows.iter().for_each(|&v| w.f128(v));
            paths
        }
        Openings::Ext(rows, paths) => {
            rows.iter().for_each(|&v| f256_row(w, v));
            paths
        }
    };
    paths.iter().flatten().for_each(|h| w.hash(h));
}

/// Encodes a WHIR opening proof under `config` in the order its verifier reads it.
pub fn encode(config: &Config, proof: &Proof) -> Vec<u8> {
    let schedule = config.schedule().expect("a secure configuration");
    let mut w = Writer::default();
    let mut msgs = proof.sumcheck.iter();
    let mut take = |w: &mut Writer, n: usize| {
        for _ in 0..n {
            let m = msgs.next().expect("a sumcheck message");
            w.f256(m[0]);
            w.f256(m[1]);
        }
    };
    proof.ood.iter().for_each(|&v| w.f256(v));
    take(&mut w, schedule.rounds[0].fold);
    for (round, rp) in schedule.rounds[1..].iter().zip(&proof.rounds) {
        rp.cap.iter().for_each(|h| w.hash(h));
        rp.ood.iter().for_each(|&v| w.f256(v));
        w.nonce(rp.pow);
        openings(&mut w, &rp.openings);
        take(&mut w, round.fold);
    }
    proof.final_poly.iter().for_each(|&v| w.f256(v));
    w.nonce(proof.final_pow);
    openings(&mut w, &proof.final_openings);
    take(&mut w, schedule.final_vars);
    assert!(msgs.next().is_none());
    return w.bytes;
}

fn embed(v: F128) -> F256 {
    return F256::new(v, F128::ZERO);
}

fn read_f256(rd: &mut Reader) -> Result<F256> {
    return rd.f256();
}

fn sample_f256(tr: &mut KeccakChallenger) -> F256 {
    return tr.sample_f256();
}

fn powers(g: F256, n: usize) -> Vec<F256> {
    let mut out = Vec::with_capacity(n);
    let mut p = g;
    for _ in 0..n {
        out.push(p);
        p *= g;
    }
    return out;
}

/// A term of the final weight: an equality at a point, or a codeword position's coordinates.
enum Term {
    Eq(F256, Vec<F256>),
    Shift(F256, Vec<F128>),
}

fn eq_table(point: &[F256]) -> Vec<F256> {
    let mut t = vec![F256::ONE];
    for &z in point {
        let hi: Vec<F256> = t.iter().map(|&a| a * z).collect();
        t.iter_mut().zip(&hi).for_each(|(a, &b)| *a += b);
        t.extend(hi);
    }
    return t;
}

struct State<'a, 'b> {
    rd: &'a mut Reader<'b>,
    claim: F256,
    challenges: Vec<F256>,
}

impl State<'_, '_> {
    fn sumcheck(&mut self, n: usize, tr: &mut KeccakChallenger) -> Result<Vec<F256>> {
        let mut alpha = Vec::with_capacity(n);
        for _ in 0..n {
            let (e1, einf) = (read_f256(self.rd)?, read_f256(self.rd)?);
            tr.observe_f256(e1);
            tr.observe_f256(einf);
            let r = sample_f256(tr);
            self.claim = self.claim + e1 + (self.claim + einf + einf * r) * r;
            alpha.push(r);
        }
        self.challenges.extend_from_slice(&alpha);
        return Ok(alpha);
    }

    /// Reads the opened rows of a committed function at the positions `words` select, checks them
    /// under its cap, and returns each position's coordinates with the folded value there.
    fn openings(&mut self, cap: &[[u8; 32]], round: &Round, alpha: &[F256], vars: usize, base: bool, words: &[F128]) -> Result<Vec<(Vec<F128>, F256)>> {
        let lanes = 1usize << round.fold;
        let width = if base { 16 } else { 32 };
        let eq = eq_table(alpha);
        let domain = Domain::new(round.log_domain);
        let depth = round.log_domain - cap.len().trailing_zeros() as usize;
        let positions: Vec<usize> = words.iter().map(|w| (w.lo as usize) & ((1 << round.log_domain) - 1)).collect();
        let mut rows = Vec::with_capacity(positions.len());
        for _ in &positions {
            rows.push(self.rd.take(lanes * width)?);
        }
        let mut out = Vec::with_capacity(positions.len());
        for (&p, row) in positions.iter().zip(rows) {
            let mut leaf = vec![0u8];
            leaf.extend_from_slice(row);
            let mut node = keccak256(&leaf);
            for l in 0..depth {
                let sibling = self.rd.hash()?;
                node = if p >> l & 1 == 0 { keccak_node(&node, &sibling) } else { keccak_node(&sibling, &node) };
            }
            if cap[p >> depth] != node {
                return Err(Reject("merkle path"));
            }
            let value = row.chunks(width).zip(&eq).fold(F256::ZERO, |acc, (c, &e)| {
                let word = |b: &[u8]| {
                    let v = u128::from_be_bytes(b.try_into().expect("sixteen bytes"));
                    F128::new(v as u64, (v >> 64) as u64)
                };
                acc + if base { e * word(c) } else { e * F256::new(word(&c[..16]), word(&c[16..])) }
            });
            out.push((domain.coordinates(p, vars), value));
        }
        return Ok(out);
    }
}

fn keccak256(bytes: &[u8]) -> [u8; 32] {
    // A leaf is a zero byte and the row's words in big-endian order, which is how calldata holds them.
    let mut le = bytes[1..].to_vec();
    le.chunks_mut(16).for_each(<[u8]>::reverse);
    return keccak_leaf(&le);
}

/// Verifies that the polynomial committed under `cap` takes `values` at `points`, reading the
/// proof from `rd`.
pub fn verify(config: &Config, cap: &[[u8; 32]], points: &[Vec<F128>], values: &[F128], rd: &mut Reader, tr: &mut KeccakChallenger) -> Result<()> {
    let schedule = config.schedule().map_err(|_| Reject("configuration"))?;
    let rounds = &schedule.rounds;
    let m = config.num_vars;
    let r0 = rounds[0];
    if cap.len() != cap_size(1 << r0.log_domain, r0.queries) || points.len() != values.len() || points.iter().any(|z| z.len() != m) {
        return Err(Reject("opening shape"));
    }
    tr.observe_label(b"flock-whir-v1");
    tr.observe_bytes(&config.to_bytes());
    tr.observe_bytes(cap.as_flattened());
    let ood_points: Vec<Vec<F256>> = (0..r0.ood).map(|_| (0..m).map(|_| sample_f256(tr)).collect()).collect();
    let ood: Vec<F256> = (0..r0.ood).map(|_| read_f256(rd)).collect::<Result<_>>()?;
    ood.iter().for_each(|&v| tr.observe_f256(v));
    tr.observe_label(b"flock-whir-open");
    tr.observe_bytes(&[points.len() as u64, 0u64].map(u64::to_le_bytes).concat());
    for (z, &v) in points.iter().zip(values) {
        z.iter().for_each(|&c| tr.observe_f256(embed(c)));
        tr.observe_f256(embed(v));
    }
    let gamma = powers(sample_f256(tr), ood.len() + values.len());
    let mut terms: Vec<Term> = Vec::new();
    let mut claim = F256::ZERO;
    for ((z, &v), &g) in ood_points.into_iter().zip(&ood).zip(&gamma) {
        claim += g * v;
        terms.push(Term::Eq(g, z));
    }
    for ((z, &v), &g) in points.iter().zip(values).zip(&gamma[ood.len()..]) {
        claim += g * v;
        terms.push(Term::Eq(g, z.iter().map(|&c| embed(c)).collect()));
    }
    let mut st = State {
        rd,
        claim,
        challenges: Vec::with_capacity(m),
    };
    let mut alpha = st.sumcheck(r0.fold, tr)?;
    let mut prev_cap = cap.to_vec();
    let mut prev = r0;
    for (i, round) in rounds[1..].iter().enumerate() {
        let n_cap = cap_size(1 << round.log_domain, round.queries);
        let cap: Vec<[u8; 32]> = (0..n_cap).map(|_| st.rd.hash()).collect::<Result<_>>()?;
        tr.observe_bytes(cap.as_flattened());
        let ood_points: Vec<Vec<F256>> = (0..round.ood).map(|_| (0..round.vars).map(|_| sample_f256(tr)).collect()).collect();
        let ood: Vec<F256> = (0..round.ood).map(|_| read_f256(st.rd)).collect::<Result<_>>()?;
        ood.iter().for_each(|&v| tr.observe_f256(v));
        let words = pow_vec(tr, st.rd.nonce()?, config.pow_bits, prev.queries)?;
        let folded = st.openings(&prev_cap, &prev, &alpha, round.vars, i == 0, &words)?;
        let gamma = powers(sample_f256(tr), ood.len() + folded.len());
        for ((z, &y), &c) in ood_points.into_iter().zip(&ood).zip(&gamma) {
            st.claim += c * y;
            terms.push(Term::Eq(c, z));
        }
        for ((coords, y), &c) in folded.into_iter().zip(&gamma[ood.len()..]) {
            st.claim += c * y;
            terms.push(Term::Shift(c, coords));
        }
        alpha = st.sumcheck(round.fold, tr)?;
        prev_cap = cap;
        prev = *round;
    }
    let final_poly: Vec<F256> = (0..1usize << schedule.final_vars).map(|_| read_f256(st.rd)).collect::<Result<_>>()?;
    final_poly.iter().for_each(|&v| tr.observe_f256(v));
    let words = pow_vec(tr, st.rd.nonce()?, config.pow_bits, prev.queries)?;
    let folded = st.openings(&prev_cap, &prev, &alpha, schedule.final_vars, rounds.len() == 1, &words)?;
    for (coords, y) in folded {
        // The final polynomial at a codeword position: its hypercube values against the position's
        // monomials, one variable at a time.
        let mut v = final_poly.clone();
        for &c in &coords {
            v = v.chunks(2).map(|p| p[0] + p[1] * c).collect();
        }
        if v[0] != y {
            return Err(Reject("final polynomial"));
        }
    }
    let r = st.sumcheck(schedule.final_vars, tr)?;
    let point = &st.challenges;
    let weight = terms.iter().fold(F256::ZERO, |acc, t| {
        acc + match t {
            Term::Eq(c, z) => *c * z.iter().zip(&point[m - z.len()..]).fold(F256::ONE, |a, (&x, &y)| a * (F256::ONE + x + y)),
            Term::Shift(c, w) => *c * w.iter().zip(&point[m - w.len()..]).fold(F256::ONE, |a, (&x, &y)| a * (F256::ONE + y * (F128::ONE + x))),
        }
    });
    let mut v = final_poly;
    for &x in &r {
        v = v.chunks(2).map(|p| p[0] + x * (p[0] + p[1])).collect();
    }
    if st.claim != v[0] * weight {
        return Err(Reject("opening sumcheck"));
    }
    return Ok(());
}
