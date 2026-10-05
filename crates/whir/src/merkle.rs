// SPDX-License-Identifier: LGPL-3.0-or-later
//! Capped BLAKE3 Merkle trees over codeword rows, one leaf per evaluation point.

use flock_prover::merkle::{
    Hash, HashKind, cap_depth, cap_layer, hash_leaf, merkle_proof_capped, merkle_tree,
    verify_merkle_proof_capped,
};

/// A Merkle tree whose commitment is its cap: the layer of nodes at a depth that makes the
/// queries' paths and the cap cost the same.
pub struct Tree {
    nodes: Vec<Hash>,
    leaves: usize,
    cap_log: usize,
}

impl Tree {
    /// The tree of `leaves` equal leaves of `bytes`, capped for `queries` openings.
    pub fn new(bytes: &[u8], leaves: usize, queries: usize) -> Tree {
        let depth = leaves.trailing_zeros() as usize;
        let nodes = merkle_tree(bytes, leaves, HashKind::Blake3);
        Tree { nodes, leaves, cap_log: cap_depth(queries, depth) }
    }

    /// The cap.
    pub fn cap(&self) -> Vec<Hash> {
        cap_layer(&self.nodes, self.leaves, self.cap_log).to_vec()
    }

    /// The path of leaf `index` up to the cap.
    pub fn path(&self, index: usize) -> Vec<Hash> {
        merkle_proof_capped(&self.nodes, self.leaves, index, self.cap_log)
    }
}

/// The cap size a tree of `leaves` leaves takes for `queries` openings.
pub fn cap_size(leaves: usize, queries: usize) -> usize {
    1 << cap_depth(queries, leaves.trailing_zeros() as usize)
}

/// Whether `leaf` sits at `index` under `cap`.
pub fn verify(cap: &[Hash], leaves: usize, leaf: &[u8], index: usize, path: &[Hash]) -> bool {
    let digest = hash_leaf(leaf, HashKind::Blake3);
    verify_merkle_proof_capped(cap, leaves, &digest, index, path, HashKind::Blake3)
}
