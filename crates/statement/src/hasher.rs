// SPDX-License-Identifier: LGPL-3.0-or-later

//! Keccak-256 as a [`Hasher`]: the original Keccak (padding byte `0x01`), not NIST SHA3-256.

use core::fmt::{self, Debug};

use tiny_keccak::{Hasher as _, Keccak};
use zeroize::Zeroize;
use zkboo::crypto::Hasher;

/// A [`Hasher`] backed by Keccak-256, producing 32-byte digests.
pub struct Keccak256Hasher {
    inner: Keccak,
}

impl Debug for Keccak256Hasher {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return f.write_str("Keccak256Hasher");
    }
}

impl Hasher for Keccak256Hasher {
    type Digest = [u8; 32];
    const DIGEST_SIZE: usize = 32;

    fn new() -> Self {
        return Self {
            inner: Keccak::v256(),
        };
    }

    fn update(&mut self, data: &[u8]) {
        self.inner.update(data);
    }

    fn finalize_into(&mut self, out: &mut Self::Digest) {
        let inner = core::mem::replace(&mut self.inner, Keccak::v256());
        inner.finalize(out);
    }
}

impl Zeroize for Keccak256Hasher {
    fn zeroize(&mut self) {
        self.inner = Keccak::v256();
    }
}
