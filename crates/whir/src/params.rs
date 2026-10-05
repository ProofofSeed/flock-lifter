// SPDX-License-Identifier: LGPL-3.0-or-later
//! WHIR parameters: the round schedule and its round-by-round soundness.

use serde::{Deserialize, Serialize};

/// Bits of the challenge field, GF(2^256).
pub const FIELD_BITS: f64 = 256.0;

/// The proximity regime the queries are counted in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Regime {
    /// Unique decoding, `δ = (1 - ρ)/2`.
    UniqueDecoding,
    /// Up to the Johnson bound, `δ = 1 - √ρ - η` with `η = √ρ/20`.
    Johnson,
}

/// The hash of the codewords' Merkle trees.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MerkleHash {
    /// BLAKE3, which Flock's circuit gadgets replay.
    #[default]
    Blake3,
    /// Keccak-256, which the EVM computes natively.
    Keccak,
}

/// The parameters of a WHIR commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Config {
    /// Variables of the committed multilinear polynomial.
    pub num_vars: usize,
    /// Variables folded per round.
    pub folding: usize,
    /// Log of the inverse rate of the initial code.
    pub log_inv_rate: usize,
    /// Target security in bits.
    pub security_bits: u32,
    /// Proof-of-work bits ground before each query phase.
    pub pow_bits: u32,
    /// Variables of the final polynomial, sent in the clear.
    pub final_vars: usize,
    /// The proximity regime.
    pub regime: Regime,
    /// The hash of the Merkle trees.
    pub merkle: MerkleHash,
}

/// One committed function of the protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Round {
    /// Variables of the function's message.
    pub vars: usize,
    /// Variables folded after it is committed, which are its interleaved lanes.
    pub fold: usize,
    /// Log of its evaluation domain's size.
    pub log_domain: usize,
    /// Queries into its codeword.
    pub queries: usize,
    /// Out-of-domain samples of it.
    pub ood: usize,
}

impl Round {
    /// Log of the inverse rate of its code.
    pub fn log_inv_rate(&self) -> usize {
        self.log_domain - (self.vars - self.fold)
    }
}

/// The round schedule of a configuration.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Schedule {
    /// The committed functions, the initial commitment first.
    pub rounds: Vec<Round>,
    /// Variables of the final polynomial.
    pub final_vars: usize,
    /// The weakest round-by-round error, in bits.
    pub security: f64,
}

/// Why a configuration was refused.
#[derive(Clone, Debug, PartialEq)]
pub enum ConfigError {
    /// The folding factor is zero, or the polynomial is no larger than the final one.
    Shape,
    /// A round's error exceeds the target: the round and the error in bits.
    Insecure(usize, f64),
}

/// The proximity parameter, per-query error in bits and list size of a code of rate `2^-log_inv_rate`.
fn proximity(regime: Regime, log_inv_rate: usize) -> (f64, f64, f64) {
    let rho = (-(log_inv_rate as f64)).exp2();
    let (delta, list) = match regime {
        Regime::UniqueDecoding => ((1.0 - rho) / 2.0, 1.0),
        Regime::Johnson => {
            let eta = rho.sqrt() / 20.0;
            (1.0 - rho.sqrt() - eta, 1.0 / (2.0 * eta * rho.sqrt()))
        }
    };
    (delta, -(1.0 - delta).log2(), list)
}

/// The mutual correlated agreement error of a code of `vars` message variables, in bits.
fn agreement_bits(regime: Regime, vars: usize, log_inv_rate: usize) -> f64 {
    let rho = (-(log_inv_rate as f64)).exp2();
    match regime {
        Regime::UniqueDecoding => FIELD_BITS - vars as f64 - log_inv_rate as f64,
        Regime::Johnson => {
            let eta = rho.sqrt() / 20.0;
            FIELD_BITS - 2.0 * vars as f64 + 7.0 * (2.0 * eta).log2()
        }
    }
}

impl Config {
    /// The round schedule, refused if any round falls short of the target security.
    pub fn schedule(&self) -> Result<Schedule, ConfigError> {
        if self.folding == 0 || self.num_vars <= self.final_vars {
            return Err(ConfigError::Shape);
        }
        let lambda = self.security_bits as f64;
        let mut rounds: Vec<Round> = Vec::new();
        let mut vars = self.num_vars;
        while vars > self.final_vars {
            let fold = self.folding.min(vars - self.final_vars);
            let lane_vars = vars - fold;
            let log_domain = match rounds.last() {
                None => lane_vars + self.log_inv_rate,
                Some(prev) => (prev.log_domain - 1).max(lane_vars + 1),
            };
            rounds.push(Round { vars, fold, log_domain, queries: 0, ood: 0 });
            vars = lane_vars;
        }
        let mut security = f64::INFINITY;
        for (i, round) in rounds.iter_mut().enumerate() {
            let (_, query_bits, list) = proximity(self.regime, round.log_inv_rate());
            let needed = (lambda - self.pow_bits as f64).max(0.0);
            round.queries = ((needed / query_bits).ceil() as usize).max(1);
            let query_error = round.queries as f64 * query_bits + self.pow_bits as f64;
            round.ood = match self.regime {
                Regime::UniqueDecoding => 0,
                Regime::Johnson => {
                    let per = FIELD_BITS + 1.0 - round.vars as f64 - 2.0 * list.log2();
                    ((lambda / per).ceil() as usize).max(1)
                }
            };
            let fold_error = agreement_bits(self.regime, round.vars, round.log_inv_rate())
                .min(FIELD_BITS - (3.0 * list).log2());
            let ood_error = match self.regime {
                Regime::UniqueDecoding => f64::INFINITY,
                Regime::Johnson => {
                    round.ood as f64 * (FIELD_BITS + 1.0 - round.vars as f64 - 2.0 * list.log2())
                }
            };
            let worst = query_error.min(fold_error).min(ood_error);
            if worst < lambda {
                return Err(ConfigError::Insecure(i, worst));
            }
            security = security.min(worst);
        }
        Ok(Schedule { rounds, final_vars: vars, security })
    }

    /// The configuration as bytes, for the transcript.
    pub fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(self).expect("serialisable")
    }
}
