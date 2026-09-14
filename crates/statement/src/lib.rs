// SPDX-License-Identifier: LGPL-3.0-or-later

//! Statement definitions shared by the prover and verifier sides of the Flock lifter.
//!
//! The circuit and crypto suite are those of the SP1 lifter, so that both lifters lift the same
//! ZKBoo proofs: BIP-32 hardened-child derivation, Keccak-256 for commitments, PRGs and challenge
//! entropy.

#![no_std]

extern crate alloc;

mod hasher;
mod journal;

use alloc::vec::Vec;
use zkboo::{
    backend::{Backend, Frontend},
    circuit::{Assertions, Circuit},
    crypto::{HashPRG, Hasher},
    prover::proof::Proof,
};
use zkboo_bip32::hardened_child_key;

pub use hasher::Keccak256Hasher;
pub use journal::{
    JournalCheckError, JournalExpectation, LIFT_JOURNAL_VERSION, LiftJournal, REQUIRED_PROOF_FORMAT_ID,
    check_journal,
};

/// Hasher used for commitments, PRGs and challenge entropy.
pub type H = Keccak256Hasher;

/// Seed PRG.
pub type PS = HashPRG<H>;

/// View PRG.
pub type PV = HashPRG<H>;

/// Seed type.
pub type S = <H as Hasher>::Digest;

/// A ZKBoo proof under the fixed crypto suite.
pub type LiftProof = Proof<S, S>;

/// Byte length of a BIP-32 chain code.
pub const CHAIN_CODE_LEN: usize = 32;

/// Byte length of a secp256k1 private key.
pub const PARENT_PRIV_LEN: usize = 32;

/// BIP-32 hardened-child-key derivation as a ZKBoo circuit.
pub struct HardenedChildCircuit {
    chain_code: Vec<u8>,
    parent_priv: Vec<u8>,
    index: u32,
}

impl HardenedChildCircuit {
    /// Creates the circuit with a genuine witness, for proving.
    pub fn with_witness(chain_code: Vec<u8>, parent_priv: Vec<u8>, index: u32) -> Self {
        assert_eq!(chain_code.len(), CHAIN_CODE_LEN, "chain code must be 32 bytes");
        assert_eq!(parent_priv.len(), PARENT_PRIV_LEN, "parent private key must be 32 bytes");
        return Self {
            chain_code,
            parent_priv,
            index,
        };
    }

    /// Creates the circuit from public parameters only, for verifying.
    pub fn public_only(chain_code: Vec<u8>, index: u32) -> Self {
        assert_eq!(chain_code.len(), CHAIN_CODE_LEN, "chain code must be 32 bytes");
        return Self {
            chain_code,
            parent_priv: alloc::vec![0u8; PARENT_PRIV_LEN],
            index,
        };
    }

    /// The parent chain code.
    pub fn chain_code(&self) -> &[u8] {
        return &self.chain_code;
    }

    /// The child index.
    pub fn index(&self) -> u32 {
        return self.index;
    }
}

impl Circuit for HardenedChildCircuit {
    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
        Assertions::scope(frontend, |_| {
            let chain_code = self
                .chain_code
                .iter()
                .map(|&b| frontend.alloc(b))
                .collect::<Vec<_>>();
            let parent_priv = self
                .parent_priv
                .iter()
                .map(|&b| frontend.input(b))
                .collect::<Vec<_>>();
            let (child_priv, child_chain_code) =
                hardened_child_key(frontend.allocator(), chain_code, parent_priv, self.index);
            frontend.output(child_priv);
            child_chain_code
                .into_iter()
                .for_each(|w| frontend.output(w));
        });
    }
}
