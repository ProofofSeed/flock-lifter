// SPDX-License-Identifier: LGPL-3.0-or-later

//! Fixed-depth Keccak Merkle trees over 32-byte words, with proofs for contiguous ranges.
//!
//! A leaf is the word itself, a node is `keccak(left ‖ right)`, and a tree of depth `d` covers
//! `2^d` words, the ones past the data being zero. A range proof lists the siblings that
//! recomputing the root from the range consumes, parent by parent, level by level, left sibling
//! before right.

use rayon::prelude::*;
use revm::primitives::{B256, keccak256};

/// `keccak(l ‖ r)`.
pub fn node(l: &B256, r: &B256) -> B256 {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(l.as_slice());
    buf[32..].copy_from_slice(r.as_slice());
    return keccak256(buf);
}

/// Roots of all-zero trees of depth `0..=depth`.
pub fn zeros(depth: usize) -> Vec<B256> {
    let mut z = vec![B256::ZERO];
    for k in 0..depth {
        z.push(node(&z[k], &z[k]));
    }
    return z;
}

/// The levels of the tree over `words`, bottom first; each level holds only the nodes above
/// data, the rest being zero-tree roots.
pub fn levels(words: &[B256], depth: usize) -> Vec<Vec<B256>> {
    assert!(words.len() <= 1usize << depth, "{} words exceed a tree of depth {depth}", words.len());
    let z = zeros(depth);
    let mut out = vec![words.to_vec()];
    for k in 0..depth {
        let below = &out[k];
        let n = below.len().div_ceil(2);
        let level: Vec<B256> = (0..n)
            .into_par_iter()
            .with_min_len(1 << 12)
            .map(|p| {
                let l = below[2 * p];
                let r = if 2 * p + 1 < below.len() { below[2 * p + 1] } else { z[k] };
                node(&l, &r)
            })
            .collect();
        out.push(level);
    }
    return out;
}

/// The root of the tree over `words`.
pub fn root(words: &[B256], depth: usize) -> B256 {
    if words.is_empty() {
        return zeros(depth)[depth];
    }
    return levels(words, depth)[depth][0];
}

fn at(levels: &[Vec<B256>], z: &[B256], k: usize, i: usize) -> B256 {
    return levels[k].get(i).copied().unwrap_or(z[k]);
}

/// The siblings proving the words `[lo, hi)` of the tree with `levels`.
pub fn range_proof(levels: &[Vec<B256>], depth: usize, lo: usize, hi: usize) -> Vec<B256> {
    assert!(lo < hi, "empty range");
    let z = zeros(depth);
    let (mut lo, mut hi) = (lo, hi);
    let mut out = Vec::new();
    for k in 0..depth {
        let (plo, phi) = (lo >> 1, hi.div_ceil(2));
        for p in plo..phi {
            if 2 * p < lo {
                out.push(at(levels, &z, k, 2 * p));
            }
            if 2 * p + 1 >= hi {
                out.push(at(levels, &z, k, 2 * p + 1));
            }
        }
        (lo, hi) = (plo, phi);
    }
    return out;
}

/// The root recomputed from words `values` at `[lo, lo + len)` and their proof.
pub fn range_root(values: &[B256], lo: usize, depth: usize, proof: &[B256]) -> B256 {
    let mut nodes = values.to_vec();
    let (mut lo, mut hi) = (lo, lo + values.len());
    let mut s = 0;
    for _ in 0..depth {
        let (plo, phi) = (lo >> 1, hi.div_ceil(2));
        let mut next = Vec::with_capacity(phi - plo);
        for p in plo..phi {
            let l = if 2 * p < lo {
                s += 1;
                proof[s - 1]
            } else {
                nodes[2 * p - lo]
            };
            let r = if 2 * p + 1 >= hi {
                s += 1;
                proof[s - 1]
            } else {
                nodes[2 * p + 1 - lo]
            };
            next.push(node(&l, &r));
        }
        nodes = next;
        (lo, hi) = (plo, phi);
    }
    assert_eq!(s, proof.len(), "proof length");
    return nodes[0];
}

/// Words of `bytes`, zero-padded to a whole word.
pub fn words_of(bytes: &[u8]) -> Vec<B256> {
    return bytes
        .chunks(32)
        .map(|c| {
            let mut w = [0u8; 32];
            w[..c.len()].copy_from_slice(c);
            B256::from(w)
        })
        .collect();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_proofs_recompute_the_root() {
        let words: Vec<B256> = (0..37u8).map(|i| B256::from([i + 1; 32])).collect();
        let depth = 8;
        let lv = levels(&words, depth);
        let r = lv[depth][0];
        for (lo, hi) in [(0, 1), (0, 37), (5, 6), (6, 7), (3, 29), (36, 37), (37, 40), (200, 256), (255, 256)] {
            let proof = range_proof(&lv, depth, lo, hi);
            let values: Vec<B256> = (lo..hi).map(|i| words.get(i).copied().unwrap_or(B256::ZERO)).collect();
            assert_eq!(range_root(&values, lo, depth, &proof), r, "range {lo}..{hi}");
        }
        assert_eq!(root(&[], depth), zeros(depth)[depth]);
    }
}
