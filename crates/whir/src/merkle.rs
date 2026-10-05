// SPDX-License-Identifier: LGPL-3.0-or-later
//! Capped Merkle trees over codeword rows, one leaf per evaluation point, on BLAKE3 or Keccak-256.

use crate::params::MerkleHash;
use flock_prover::merkle::{
    Hash, HashKind, cap_depth, cap_layer, hash_leaf, merkle_proof_capped, merkle_tree, verify_merkle_proof_capped,
};
use rayon::prelude::*;
use tiny_keccak::{Hasher, Keccak};

/// A Merkle tree whose commitment is its cap: the layer of nodes at a depth that makes the
/// queries' paths and the cap cost the same.
pub struct Tree {
    nodes: Nodes,
    leaves: usize,
    cap_log: usize,
}

enum Nodes {
    Blake3(Vec<Hash>),
    Keccak(Vec<Vec<Hash>>),
}

fn keccak(tag: u8, parts: &[&[u8]]) -> Hash {
    let mut k = Keccak::v256();
    k.update(&[tag]);
    for p in parts {
        k.update(p);
    }
    let mut out = [0u8; 32];
    k.finalize(&mut out);
    return out;
}

/// The Keccak-256 leaf digest of a row of 16-byte field words: a zero byte, then every word in
/// big-endian order.
pub fn keccak_leaf(row: &[u8]) -> Hash {
    let mut be = row.to_vec();
    be.chunks_mut(16).for_each(<[u8]>::reverse);
    return keccak(0, &[&be]);
}

/// The Keccak-256 digest of two children: a one byte, then the children.
pub fn keccak_node(left: &Hash, right: &Hash) -> Hash {
    return keccak(1, &[left, right]);
}

impl Tree {
    /// The tree of `leaves` equal leaves of `bytes`, capped for `queries` openings.
    pub fn new(bytes: &[u8], leaves: usize, queries: usize, hash: MerkleHash) -> Tree {
        let depth = leaves.trailing_zeros() as usize;
        let cap_log = cap_depth(queries, depth);
        let nodes = match hash {
            MerkleHash::Blake3 => Nodes::Blake3(merkle_tree(bytes, leaves, HashKind::Blake3)),
            MerkleHash::Keccak => {
                let mut levels = vec![bytes.par_chunks(bytes.len() / leaves).map(keccak_leaf).collect::<Vec<Hash>>()];
                while levels.last().expect("a level").len() > 1 {
                    let next = levels.last().expect("a level").par_chunks(2).map(|p| keccak_node(&p[0], &p[1])).collect();
                    levels.push(next);
                }
                Nodes::Keccak(levels)
            }
        };
        return Tree { nodes, leaves, cap_log };
    }

    /// The cap.
    pub fn cap(&self) -> Vec<Hash> {
        return match &self.nodes {
            Nodes::Blake3(nodes) => cap_layer(nodes, self.leaves, self.cap_log).to_vec(),
            Nodes::Keccak(levels) => levels[levels.len() - 1 - self.cap_log].clone(),
        };
    }

    /// The path of leaf `index` up to the cap.
    pub fn path(&self, index: usize) -> Vec<Hash> {
        return match &self.nodes {
            Nodes::Blake3(nodes) => merkle_proof_capped(nodes, self.leaves, index, self.cap_log),
            Nodes::Keccak(levels) => {
                (0..levels.len() - 1 - self.cap_log).map(|l| levels[l][(index >> l) ^ 1]).collect()
            }
        };
    }
}

/// The cap size a tree of `leaves` leaves takes for `queries` openings.
pub fn cap_size(leaves: usize, queries: usize) -> usize {
    return 1 << cap_depth(queries, leaves.trailing_zeros() as usize);
}

/// Whether `leaf` sits at `index` under `cap`.
pub fn verify(cap: &[Hash], leaves: usize, leaf: &[u8], index: usize, path: &[Hash], hash: MerkleHash) -> bool {
    match hash {
        MerkleHash::Blake3 => {
            let digest = hash_leaf(leaf, HashKind::Blake3);
            return verify_merkle_proof_capped(cap, leaves, &digest, index, path, HashKind::Blake3);
        }
        MerkleHash::Keccak => {
            let depth = leaves.trailing_zeros() as usize;
            if !cap.len().is_power_of_two() || path.len() + cap.len().trailing_zeros() as usize != depth {
                return false;
            }
            let mut node = keccak_leaf(leaf);
            for (l, sibling) in path.iter().enumerate() {
                node = if (index >> l) & 1 == 0 { keccak_node(&node, sibling) } else { keccak_node(sibling, &node) };
            }
            return cap[index >> path.len()] == node;
        }
    }
}
