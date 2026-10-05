// SPDX-License-Identifier: LGPL-3.0-or-later

//! The calldata encoding of a wrapped lift, laid out in the order its verifier reads it.

use flock_prover::{pcs::MergedInner, tower::WrapProof};

use crate::{calldata::Writer, wrap::vk::Vk};

fn rounds(w: &mut Writer, rounds: &[(flock_prover::field::F128, flock_prover::field::F128)], nonces: &[u64]) {
    assert_eq!(rounds.len(), nonces.len());
    for (&(a, b), &n) in rounds.iter().zip(nonces) {
        w.f128(a);
        w.f128(b);
        w.nonce(n);
    }
}

/// Encodes a wrap's outer proof up to its commitment's opening, which is returned apart.
pub fn encode_outer(vk: &Vk, proof: &WrapProof, live: flock_prover::field::F128, masked: flock_prover::field::F128) -> (Vec<u8>, Vec<u8>) {
    let mut w = Writer::default();
    assert_eq!(proof.public.len(), vk.num_public);
    for (i, &v) in proof.public.iter().enumerate().skip(vk.fixed.len()) {
        if !vk.is_published(i) {
            w.f128(v);
        }
    }
    proof.commitment.cap.iter().for_each(|h| w.hash(h));
    w.hash(&flock_prover::union::publics_digest(&proof.public));
    let p = &proof.proof;
    let b = p.boolean.as_ref().expect("a Boolean class");
    let zc = &b.zerocheck;
    let n = vk.m_bool - 6;
    assert_eq!(zc.multilinear_rounds.len(), n);
    assert_eq!(zc.grinding_nonces.len(), 2 + n);
    w.nonce(zc.grinding_nonces[0]);
    zc.round1_ab.iter().for_each(|&v| w.f128(v));
    zc.round1_c.iter().for_each(|&v| w.f128(v));
    w.nonce(zc.grinding_nonces[1]);
    w.f128(zc.final_c_eval);
    rounds(&mut w, &zc.multilinear_rounds, &zc.grinding_nonces[2..]);
    w.f128(zc.final_a_eval);
    w.f128(zc.final_b_eval);
    let lc = &b.lincheck;
    let pins = vk.bools.iter().filter(|t| t.pin.is_some()).count();
    assert_eq!(lc.grinding_nonces.len(), 1 + pins + lc.rounds.len() + 1);
    lc.grinding_nonces[..1 + pins].iter().for_each(|&x| w.nonce(x));
    rounds(&mut w, &lc.rounds, &lc.grinding_nonces[1 + pins..1 + pins + lc.rounds.len()]);
    lc.z_partial.iter().for_each(|&v| w.f128(v));
    w.nonce(lc.grinding_nonces[1 + pins + lc.rounds.len()]);
    assert_eq!(lc.matrix_evals.len(), vk.bools.len());
    for &(a, b) in &lc.matrix_evals {
        w.f128(a);
        w.f128(b);
    }
    let g = &p.wiring.gkr;
    let mut nonces = g.grinding_nonces.iter();
    let mut next = || *nonces.next().expect("a nonce");
    w.nonce(next());
    w.f128(g.top_lhs);
    w.f128(g.top_rhs);
    assert_eq!(g.layers.len(), vk.mu);
    for layer in &g.layers {
        w.nonce(next());
        for &(a, b) in &layer.rounds {
            w.f128(a);
            w.f128(b);
            w.nonce(next());
        }
        [layer.vl0, layer.vl1, layer.vr0, layer.vr1].iter().for_each(|&v| w.f128(v));
        w.nonce(next());
    }
    assert!(nonces.next().is_none());
    [g.f_eval, g.g_eval, g.s_sigma_eval, live, masked].iter().for_each(|&v| w.f128(v));
    assert_eq!(p.wiring.gather.len(), vk.gate_cols.len());
    p.wiring.gather.iter().for_each(|&v| w.f128(v));
    let e = p.element.as_ref().expect("an element class");
    let ez = &e.zerocheck;
    assert_eq!(ez.grinding_nonces.len(), 1 + ez.rounds.len());
    w.nonce(ez.grinding_nonces[0]);
    rounds(&mut w, &ez.rounds, &ez.grinding_nonces[1..]);
    [ez.ea, ez.eb, ez.ec].iter().for_each(|&v| w.f128(v));
    let el = &e.lincheck;
    assert_eq!(el.grinding_nonces.len(), 1 + el.rounds.len());
    w.nonce(el.grinding_nonces[0]);
    rounds(&mut w, &el.rounds, &el.grinding_nonces[1..]);
    w.f128(el.z_eval);
    assert_eq!(el.matrix_evals.len(), vk.elems.len());
    for &(a, b) in &el.matrix_evals {
        w.f128(a);
        w.f128(b);
    }
    let o = &p.pcs_open;
    assert_eq!(o.ring_switches.len(), 2);
    for rs in &o.ring_switches {
        rs.s_hat_v.iter().for_each(|&v| w.f128(v));
        w.nonce(rs.grinding_nonce);
    }
    assert_eq!(o.batching_nonces.len(), 1);
    w.nonce(o.batching_nonces[0]);
    rounds(&mut w, &o.merged_rounds, &o.merged_round_nonces);
    w.f128(o.q_eval);
    let f = &o.frobenius;
    assert_eq!(f.values.len(), 2);
    f.values.iter().flatten().for_each(|&v| w.f128(v));
    f.group_values.iter().for_each(|&v| w.f128(v));
    w.nonce(f.gamma_grinding_nonce);
    rounds(&mut w, &f.rounds, &f.round_grinding_nonces);
    w.f128(f.anchor.v);
    rounds(&mut w, &f.anchor.rounds, &f.anchor.grinding_nonces);
    let MergedInner::Outer(bytes) = &o.inner else { panic!("a wrap opens through an outer commitment") };
    return (w.bytes, bytes.clone());
}
