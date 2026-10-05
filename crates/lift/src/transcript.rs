// SPDX-License-Identifier: LGPL-3.0-or-later

//! The Fiat-Shamir transcript every chunk proof is made under: Flock's operation framing over a
//! Keccak-256 hash chain, which a contract can replay with the `KECCAK256` opcode alone.
//!
//! Flock's own transcript keeps a running hash state and finalises a copy of it at every
//! challenge. The EVM cannot resume a hash state, so this one keeps a 32-byte chaining value
//! and a buffer of pending bytes: a squeeze first folds the buffer into the chaining value, then
//! expands the chaining value into as many output blocks as it needs.
//!
//! - an operation absorbs Flock's 16-byte header — op, kind, six zero bytes, then the length —
//!   followed by its payload zero-padded to a multiple of 16 bytes, so the buffer's length is
//!   always a multiple of 16;
//! - a field element is its 128-bit value in big-endian order, `hi` then `lo`;
//! - folding sets `h ← keccak256(h ‖ buffer)` and empties the buffer;
//! - output block `j` of a squeeze is `keccak256(h ‖ u64_be(j))`, and a squeeze of `n` field
//!   elements reads them in order from the concatenated blocks;
//! - a proof of work over `bits` bits folds the buffer, accepts `nonce` when
//!   `keccak256(h ‖ u64_be(nonce) ‖ u64_be(bits))` starts with `bits` zero bits, and absorbs the
//!   nonce as an `OP_BYTES` operation of eight big-endian bytes.
//!
//! Chain inputs are 32 bytes plus a multiple of 16, output blocks hash 40 bytes and proofs of
//! work 48, so no two of the three roles ever hash an input of the same length.

use flock_prover::{
    challenger::{Challenger, KIND_SCALAR, KIND_SLICE, OP_BYTES, OP_DOMAIN, OP_LABEL, OP_OBSERVE, OP_SQUEEZE},
    field::F128,
};
use rayon::prelude::*;
use tiny_keccak::{Hasher, Keccak};

/// Whether `POFSEED_TRANSCRIPT_TRACE` asks for every fold to be printed.
fn tracing() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    return *ON.get_or_init(|| std::env::var_os("POFSEED_TRANSCRIPT_TRACE").is_some());
}

/// Nonces a grinding worker tries between checks for a solution found elsewhere.
const GRIND_CHUNK: u64 = 1 << 12;

fn keccak(parts: &[&[u8]]) -> [u8; 32] {
    let mut k = Keccak::v256();
    for p in parts {
        k.update(p);
    }
    let mut out = [0u8; 32];
    k.finalize(&mut out);
    return out;
}

fn f128_bytes(v: F128) -> [u8; 16] {
    return (((v.hi as u128) << 64) | v.lo as u128).to_be_bytes();
}

fn f128_from(bytes: &[u8]) -> F128 {
    let v = u128::from_be_bytes(bytes.try_into().expect("sixteen bytes"));
    return F128::new(v as u64, (v >> 64) as u64);
}

/// Whether the proof of work `nonce` over `bits` bits is valid at chaining value `h`.
pub fn pow_ok(h: &[u8; 32], nonce: u64, bits: u32) -> bool {
    if bits == 0 {
        return nonce == 0;
    }
    let d = keccak(&[h, &nonce.to_be_bytes(), &(bits as u64).to_be_bytes()]);
    let v = u128::from_be_bytes(d[..16].try_into().expect("sixteen bytes"));
    return bits <= 128 && v.leading_zeros() >= bits;
}

/// A Keccak-256 hash-chain Fiat-Shamir transcript.
#[derive(Clone, Debug)]
pub struct KeccakChallenger {
    h: [u8; 32],
    buf: Vec<u8>,
}

impl KeccakChallenger {
    /// A transcript under the domain-separation tag `domain`.
    pub fn new(domain: &[u8]) -> Self {
        let mut c = Self {
            h: [0u8; 32],
            buf: Vec::new(),
        };
        c.header(OP_DOMAIN, 0, domain.len() as u64);
        c.padded(domain);
        return c;
    }

    fn header(&mut self, op: u8, kind: u8, len: u64) {
        let mut h = [0u8; 16];
        h[0] = op;
        h[1] = kind;
        h[8..].copy_from_slice(&len.to_be_bytes());
        self.buf.extend_from_slice(&h);
    }

    fn padded(&mut self, bytes: &[u8]) {
        self.buf.extend_from_slice(bytes);
        let rem = bytes.len() % 16;
        if rem != 0 {
            self.buf.extend_from_slice(&[0u8; 16][..16 - rem]);
        }
    }

    fn fold(&mut self) -> [u8; 32] {
        if tracing() {
            let ops: Vec<String> = self.buf.chunks(16).map(|c| format!("{:02x}{:02x}", c[0], c[1])).collect();
            eprintln!("[transcript] fold {} bytes, chunk heads {}", self.buf.len(), ops.join(" "));
        }
        self.h = keccak(&[&self.h, &self.buf]);
        self.buf.clear();
        return self.h;
    }

    fn squeeze(&mut self, n: usize) -> Vec<F128> {
        let h = self.fold();
        let blocks: Vec<[u8; 32]> = (0..n.div_ceil(2) as u64).map(|j| keccak(&[&h, &j.to_be_bytes()])).collect();
        let bytes = blocks.as_flattened();
        return (0..n).map(|i| f128_from(&bytes[16 * i..16 * i + 16])).collect();
    }

    fn absorb_nonce(&mut self, nonce: u64) {
        self.header(OP_BYTES, 0, 8);
        self.padded(&nonce.to_be_bytes());
    }

    /// The chaining value, with the pending bytes folded in.
    pub fn digest(&mut self) -> [u8; 32] {
        return self.fold();
    }
}

impl Challenger for KeccakChallenger {
    fn publics_commitment(&self, public: &[F128]) -> Option<[u8; 32]> {
        let bytes: Vec<u8> = public.iter().flat_map(|&v| f128_bytes(v)).collect();
        return Some(keccak(&[&bytes]));
    }

    fn observe_label(&mut self, label: &[u8]) {
        self.header(OP_LABEL, 0, label.len() as u64);
        self.padded(label);
    }

    fn observe_f128(&mut self, value: F128) {
        self.header(OP_OBSERVE, KIND_SCALAR, 1);
        self.buf.extend_from_slice(&f128_bytes(value));
    }

    fn observe_f128_slice(&mut self, values: &[F128]) {
        self.header(OP_OBSERVE, KIND_SLICE, values.len() as u64);
        for &v in values {
            self.buf.extend_from_slice(&f128_bytes(v));
        }
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.header(OP_BYTES, 0, bytes.len() as u64);
        self.padded(bytes);
    }

    fn sample_f128(&mut self) -> F128 {
        self.header(OP_SQUEEZE, KIND_SCALAR, 1);
        return self.squeeze(1)[0];
    }

    fn sample_f128_vec(&mut self, n: usize) -> Vec<F128> {
        self.header(OP_SQUEEZE, KIND_SLICE, n as u64);
        return self.squeeze(n);
    }

    fn grind_pow(&mut self, bits: u32) -> u64 {
        let h = self.fold();
        let nonce = if bits == 0 {
            0
        } else {
            let mut start = 0u64;
            loop {
                let found = (0..16u64).into_par_iter().find_map_first(|w| {
                    let base = start + w * GRIND_CHUNK;
                    (base..base + GRIND_CHUNK).find(|&n| pow_ok(&h, n, bits))
                });
                if let Some(n) = found {
                    break n;
                }
                start += 16 * GRIND_CHUNK;
            }
        };
        self.absorb_nonce(nonce);
        return nonce;
    }

    fn verify_pow(&mut self, nonce: u64, bits: u32) -> bool {
        let h = self.fold();
        let ok = pow_ok(&h, nonce, bits);
        self.absorb_nonce(nonce);
        return ok;
    }

    fn fork_from_seed(&self, seed: [F128; 2], label: &'static [u8]) -> Self {
        let mut child = Self::new(label);
        child.observe_f128(seed[0]);
        child.observe_f128(seed[1]);
        return child;
    }
}
