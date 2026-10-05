// SPDX-License-Identifier: LGPL-3.0-or-later
//! WHIR as the outer commitment of Flock's union-circuit prover.

use crate::params::{Config, MerkleHash, Regime};
use crate::whir::{self, Commitment, Committed, Proof};
use flock_prover::challenger::Challenger;
use flock_prover::field::{F128, F256};
use flock_prover::merkle::Hash;
use flock_prover::pcs::OuterPcs;
use std::any::Any;

/// WHIR's parameters for a dense stack of any size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WhirOuter {
    folding: usize,
    log_inv_rate: usize,
    regime: Regime,
    final_vars: usize,
    pow_bits: u32,
    security_bits: u32,
    merkle: MerkleHash,
}

impl WhirOuter {
    /// The parameters, validated against a stack of `2^20` words.
    pub fn new(
        folding: usize,
        log_inv_rate: usize,
        regime: Regime,
        final_vars: usize,
        pow_bits: u32,
        security_bits: u32,
    ) -> WhirOuter {
        let outer = WhirOuter {
            folding,
            log_inv_rate,
            regime,
            final_vars,
            pow_bits,
            security_bits,
            merkle: MerkleHash::Blake3,
        };
        outer.config(20).schedule().expect("secure WHIR parameters");
        outer
    }

    /// Folding factor 4, rate 1/2, the Johnson regime, 16 bits of grinding and 128 bits of
    /// security.
    pub fn standard() -> WhirOuter {
        WhirOuter::new(4, 1, Regime::Johnson, 6, 16, 128)
    }

    /// The same parameters with Merkle trees on `merkle`.
    pub fn with_merkle(mut self, merkle: MerkleHash) -> WhirOuter {
        self.merkle = merkle;
        self
    }

    /// The configuration for a stack of `2^num_vars` words.
    pub fn config(&self, num_vars: usize) -> Config {
        Config {
            num_vars,
            folding: self.folding,
            log_inv_rate: self.log_inv_rate,
            security_bits: self.security_bits,
            pow_bits: self.pow_bits,
            final_vars: self.final_vars.min(num_vars),
            regime: self.regime,
            merkle: self.merkle,
        }
    }
}

fn embed(point: &[F128]) -> Vec<F256> {
    point.iter().map(|&c| F256::new(c, F128::ZERO)).collect()
}

impl OuterPcs for WhirOuter {
    fn commit(&self, words: &[F128]) -> (Vec<Hash>, Box<dyn Any + Send + Sync>) {
        assert!(words.len().is_power_of_two(), "the dense stack spans a hypercube");
        let config = self.config(words.len().trailing_zeros() as usize);
        let (commitment, committed) =
            whir::commit(&config, words.to_vec()).expect("secure WHIR parameters");
        (commitment.cap, Box::new(committed))
    }

    fn open(
        &self,
        state: Box<dyn Any + Send + Sync>,
        point: &[F128],
        challenger: &mut dyn Challenger,
    ) -> Vec<u8> {
        let committed = *state.downcast::<Committed>().expect("a WHIR commitment's state");
        let (_, proof) = whir::open(committed, &[embed(point)], challenger);
        proof.to_bytes()
    }

    fn verify(
        &self,
        cap: &[Hash],
        point: &[F128],
        value: F128,
        proof: &[u8],
        challenger: &mut dyn Challenger,
    ) -> bool {
        let Ok(proof) = bincode::deserialize::<Proof>(proof) else {
            return false;
        };
        whir::verify(
            &self.config(point.len()),
            &Commitment { cap: cap.to_vec() },
            &[embed(point)],
            &[F256::new(value, F128::ZERO)],
            &proof,
            challenger,
        )
        .is_ok()
    }
}
