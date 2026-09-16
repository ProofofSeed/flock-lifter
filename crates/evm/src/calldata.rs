// SPDX-License-Identifier: LGPL-3.0-or-later

//! The calldata encoding of a lifted proof, which the contract and the mirror both read with a
//! single forward cursor.
//!
//! A chunk is laid out in exactly the order its verifier consumes it, so no offsets are carried:
//! every count follows from the chunk's size and its PCS configuration. Field elements are
//! sixteen bytes, big-endian in their 128-bit value, except where the verifier hashes their
//! memory image — the rows a Ligerito opening reveals and the words a block publishes — which
//! are sixteen bytes in Flock's native layout, `lo` then `hi`, each little-endian. A GF(2^256)
//! element is its `c1` coordinate then its `c0` coordinate, a hash is thirty-two bytes and a
//! proof-of-work nonce eight, big-endian.

use flock_prover::{
    field::{F128, F256},
    pcs::ligerito::{LigeritoProof, SumcheckMessage256},
};
use pofseed_flock_lift::{
    chunk_rm::{ChunkProofRm, pcs_params},
    lift::LiftedProof,
};

/// Log-size of a response block.
pub const K_LOG: usize = 28;

/// Chunk sizes, in committed variables, the calldata format covers.
pub const M_RANGE: core::ops::RangeInclusive<usize> = 31..=35;

/// An appending calldata writer.
#[derive(Default)]
pub struct Writer {
    /// The bytes written so far.
    pub bytes: Vec<u8>,
}

impl Writer {
    /// Appends a field element as its big-endian value.
    pub fn f128(&mut self, v: F128) {
        self.bytes.extend_from_slice(&(((v.hi as u128) << 64) | v.lo as u128).to_be_bytes());
    }

    /// Appends a field element in Flock's native memory layout.
    pub fn f128_native(&mut self, v: F128) {
        self.bytes.extend_from_slice(&v.lo.to_le_bytes());
        self.bytes.extend_from_slice(&v.hi.to_le_bytes());
    }

    /// Appends an extension element, `c1` then `c0`.
    pub fn f256(&mut self, v: F256) {
        self.f128(v.c1);
        self.f128(v.c0);
    }

    /// Appends a 32-byte hash.
    pub fn hash(&mut self, h: &[u8; 32]) {
        self.bytes.extend_from_slice(h);
    }

    /// Appends a proof-of-work nonce.
    pub fn nonce(&mut self, n: u64) {
        self.bytes.extend_from_slice(&n.to_be_bytes());
    }

    /// Appends raw bytes.
    pub fn raw(&mut self, b: &[u8]) {
        self.bytes.extend_from_slice(b);
    }
}

/// Committed variables of a chunk of `rows` blocks.
pub fn chunk_m(rows: usize) -> usize {
    return K_LOG + (rows.next_power_of_two().trailing_zeros() as usize).max(3);
}

struct Lists<'a, T> {
    items: &'a [T],
    at: usize,
}

impl<'a, T> Lists<'a, T> {
    fn new(items: &'a [T]) -> Self {
        return Self { items, at: 0 };
    }

    fn next(&mut self) -> &'a T {
        let v = &self.items[self.at];
        self.at += 1;
        return v;
    }

    fn done(&self) -> bool {
        return self.at == self.items.len();
    }
}

fn message(w: &mut Writer, msg: &SumcheckMessage256) {
    w.f256(msg.u_0);
    w.f256(msg.u_2);
}

fn rows(w: &mut Writer, rows: &[Vec<F128>], width: usize, paths: &[[u8; 32]]) {
    for row in rows {
        assert_eq!(row.len(), width, "opened row width");
        for &v in row {
            w.f128_native(v);
        }
    }
    for h in paths {
        w.hash(h);
    }
}

fn ligerito(w: &mut Writer, m: usize, proof: &LigeritoProof) {
    let config = pcs_params(m).ligerito_verifier_config().expect("registered configuration");
    assert!(proof.sumcheck_transcript.is_empty() && proof.fold_grinding_nonces.is_empty());
    let mut msgs = Lists::new(&proof.sumcheck_transcript_f256);
    let mut oods = Lists::new(&proof.ood_values);
    let mut claim_nonces = Lists::new(&proof.claim_batch_grinding_nonces);
    let mut consistency_nonces = Lists::new(&proof.consistency_batch_grinding_nonces);
    let mut query_nonces = Lists::new(&proof.grinding_nonces);
    let mut caps = Lists::new(&proof.recursive_caps);
    let mut openings = Lists::new(&proof.recursive_proofs);
    for _ in 0..config.ood_samples[0] {
        w.f128(*oods.next());
        w.nonce(*claim_nonces.next());
    }
    message(w, msgs.next());
    for _ in 0..config.initial_k {
        message(w, msgs.next());
    }
    let cap = caps.next();
    assert_eq!(cap.len(), 1 << config.stratified[1].cap_depth());
    cap.iter().for_each(|h| w.hash(h));
    for _ in 0..config.ood_samples[1] {
        w.f128(*oods.next());
        message(w, msgs.next());
        w.nonce(*claim_nonces.next());
    }
    w.nonce(*query_nonces.next());
    w.nonce(*consistency_nonces.next());
    assert_eq!(proof.initial_proof.opened_rows.len(), config.queries[0]);
    rows(w, &proof.initial_proof.opened_rows, 1 << config.initial_k, &proof.initial_proof.merkle_proof);
    message(w, msgs.next());
    w.nonce(*claim_nonces.next());
    let rounds = config.recursive_steps;
    for i in 0..rounds {
        for _ in 0..config.recursive_ks[i] {
            message(w, msgs.next());
        }
        let level = i + 1;
        let width = 1 << config.recursive_ks[i];
        if i + 1 == rounds {
            proof.final_proof.yr.iter().for_each(|&v| w.f128(v));
            w.nonce(*query_nonces.next());
            w.nonce(*consistency_nonces.next());
            assert_eq!(proof.final_proof.opened_rows.len(), config.queries[level]);
            rows(w, &proof.final_proof.opened_rows, width, &proof.final_proof.merkle_proof);
            w.nonce(*claim_nonces.next());
            break;
        }
        let cap = caps.next();
        assert_eq!(cap.len(), 1 << config.stratified[level + 1].cap_depth());
        cap.iter().for_each(|h| w.hash(h));
        for _ in 0..config.ood_samples[level + 1] {
            w.f128(*oods.next());
            message(w, msgs.next());
            w.nonce(*claim_nonces.next());
        }
        w.nonce(*query_nonces.next());
        w.nonce(*consistency_nonces.next());
        let opening = openings.next();
        assert_eq!(opening.opened_rows.len(), config.queries[level]);
        rows(w, &opening.opened_rows, width, &opening.merkle_proof);
        message(w, msgs.next());
        w.nonce(*claim_nonces.next());
    }
    assert!(msgs.done() && oods.done() && claim_nonces.done() && consistency_nonces.done());
    assert!(query_nonces.done() && caps.done() && openings.done());
}

/// Encodes one chunk proof over `rows` blocks.
pub fn encode_chunk(chunk: &ChunkProofRm, rows: usize) -> Vec<u8> {
    let m = chunk_m(rows);
    assert!(M_RANGE.contains(&m));
    assert!(chunk.commitment.params == pcs_params(m), "commitment parameters");
    assert!(chunk.opening.ligerito.initial_cap == chunk.commitment.cap, "initial cap");
    let mut w = Writer::default();
    chunk.commitment.cap.iter().for_each(|h| w.hash(h));
    let zc = &chunk.zerocheck;
    assert_eq!(zc.grinding_nonces.len(), 2 + m - 6);
    assert_eq!(zc.multilinear_rounds.len(), m - 6);
    w.nonce(zc.grinding_nonces[0]);
    zc.round1_ab.iter().for_each(|&v| w.f128(v));
    zc.round1_c.iter().for_each(|&v| w.f128(v));
    w.nonce(zc.grinding_nonces[1]);
    w.f128(zc.final_c_eval);
    for (i, &(e1, einf)) in zc.multilinear_rounds.iter().enumerate() {
        w.f128(e1);
        w.f128(einf);
        w.nonce(zc.grinding_nonces[2 + i]);
    }
    w.f128(zc.final_a_eval);
    w.f128(zc.final_b_eval);
    let lc = &chunk.lincheck;
    assert_eq!(lc.rounds.len(), K_LOG - 6);
    assert_eq!(lc.grinding_nonces.len(), 3 + lc.rounds.len());
    assert!(lc.matrix_evals.is_empty());
    w.nonce(lc.grinding_nonces[0]);
    w.nonce(lc.grinding_nonces[1]);
    for (i, &(e1, einf)) in lc.rounds.iter().enumerate() {
        w.f128(e1);
        w.f128(einf);
        w.nonce(lc.grinding_nonces[2 + i]);
    }
    lc.z_partial.iter().for_each(|&v| w.f128(v));
    w.nonce(lc.grinding_nonces[2 + lc.rounds.len()]);
    let op = &chunk.opening;
    assert_eq!(op.ring_switches.len(), 3);
    for rs in &op.ring_switches {
        rs.s_hat_v.iter().for_each(|&v| w.f128(v));
        w.nonce(rs.grinding_nonce);
    }
    assert_eq!(op.batching_nonces.len(), 1);
    w.nonce(op.batching_nonces[0]);
    ligerito(&mut w, m, &op.ligerito);
    return w.bytes;
}

/// Encodes a lifted proof: the chunk size and response count, the published words and unopened
/// digest of every response, then every chunk proof prefixed by its length.
pub fn encode_lift(lifted: &LiftedProof) -> Vec<u8> {
    let mut w = Writer::default();
    let n = lifted.words.len();
    w.raw(&lifted.chunk.to_be_bytes());
    w.raw(&(n as u32).to_be_bytes());
    for words in &lifted.words {
        words.iter().for_each(|&v| w.f128_native(v));
    }
    for d in &lifted.unopened {
        w.hash(d);
    }
    for (i, c) in lifted.chunks.iter().enumerate() {
        let rows = (n - i * lifted.chunk as usize).min(lifted.chunk as usize);
        let bytes = encode_chunk(c, rows);
        w.raw(&(bytes.len() as u32).to_be_bytes());
        w.raw(&bytes);
    }
    return w.bytes;
}
