// SPDX-License-Identifier: LGPL-3.0-or-later

//! Host-side helpers for the Flock lifter: the development statement fixture and proof generation.

use pofseed_flock_lift_statement::{H, HardenedChildCircuit, PS, PV, S};
use zkboo::{
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, proof::Response, views::OwnedFlexibleWordTriplePool},
    verifier::replay::OwnedFlexibleWordPairPool,
    word::Words,
};
pub use zkboo_bip32::HARDENED_OFFSET;

/// Executor-side word pool.
pub type WP = OwnedFlexibleWordPool<usize>;
/// Prover-side word-triple pool.
pub type WTP = OwnedFlexibleWordTriplePool<usize>;
/// Verifier-side word-pair pool.
pub type WPP = OwnedFlexibleWordPairPool<usize>;

/// Repetitions needed for `(2/3)^n <= 2^-2b`, where `b` is a post-quantum security level in bits.
pub const fn n_eps(pq_security_bits: usize) -> usize {
    const NUM: u128 = 1_709_511_291_351_455;
    const DEN: u128 = 1_000_000_000_000_000;
    let two_b = (2 * pq_security_bits) as u128;
    return ((two_b * NUM + (DEN - 1)) / DEN) as usize;
}

/// Decodes a hex string.
pub fn from_hex(s: &str) -> Vec<u8> {
    return (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect();
}

/// BIP-32 test vector 1, chain m → m/0H, as `(parent_priv, chain_code)`.
pub fn bip32_vector_1() -> (Vec<u8>, Vec<u8>) {
    let parent_priv = from_hex("e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35");
    let chain_code = from_hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    return (parent_priv, chain_code);
}

/// Builds the vector-1 hardened-child circuit, its output, and a genuine proof of `num_iters`
/// responses bound to `binding`.
pub fn vector_1_proof(
    num_iters: usize,
    seed_entropy: &[u8],
    binding: &[u8],
) -> (HardenedChildCircuit, Words, Vec<Response<S, S>>) {
    let (parent_priv, chain_code) = bip32_vector_1();
    let circuit = HardenedChildCircuit::with_witness(chain_code, parent_priv, HARDENED_OFFSET);
    let output = exec::<_, WP, _>(&circuit, ExecOptions::new());
    let proof = par_prove::<_, H, PS, PV, S, WTP>(&circuit, num_iters, seed_entropy, binding);
    return (circuit, output, proof);
}
