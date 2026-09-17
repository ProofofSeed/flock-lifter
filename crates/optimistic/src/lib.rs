// SPDX-License-Identifier: LGPL-3.0-or-later

//! Optimistic verification of a Flock lift on Ethereum: the verifier contracts' execution as a
//! trace of EVM steps with committed states, and the off-chain side of a dispute game over it.

pub mod deploy;
pub mod fuzz;
pub mod game;
pub mod machine;
pub mod merkle;
pub mod scenario;
pub mod sim;
pub mod trace;
pub mod vm;
