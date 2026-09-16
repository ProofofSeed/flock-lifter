// SPDX-License-Identifier: LGPL-3.0-or-later

//! The Flock lifter's Ethereum verifier: the calldata encoding of a lifted proof, a Rust mirror
//! of the contract's verification, and an in-process EVM that runs the contract and meters it.

pub mod calldata;
pub mod evm;
pub mod mirror;
