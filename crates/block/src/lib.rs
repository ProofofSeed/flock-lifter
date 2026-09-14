// SPDX-License-Identifier: LGPL-3.0-or-later

//! The response block of the Flock lifter: the verification of one ZKBoo response as one row of
//! a Boolean R1CS table, with its witness generator and its structured lincheck.

pub mod form;
pub mod keccak;
pub mod layout;
pub mod program;
pub mod replay;
