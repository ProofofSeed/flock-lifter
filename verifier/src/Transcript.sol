// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// The lifter's Fiat-Shamir transcript, byte for byte: Flock's operation framing over a
/// Keccak-256 hash chain (see `crates/lift/src/transcript.rs`).
///
/// A transcript is a memory region holding the chaining value, the pending length, then the
/// pending bytes, so a fold hashes one contiguous range. Every failed proof of work reverts.
library Transcript {
    uint256 internal constant CAPACITY = 1 << 17;
    /// The most bytes one `CALLDATACOPY` moves, so that no single step of a disputed verification
    /// carries a large witness.
    uint256 internal constant COPY = 1 << 14;
    uint256 internal constant M128 = 0xffffffffffffffffffffffffffffffff;

    error ProofOfWork();

    /// A transcript under a domain tag read from calldata.
    function create(uint256 domainOffset, uint256 domainLength) internal pure returns (uint256 tr) {
        assembly ("memory-safe") {
            tr := mload(0x40)
            mstore(0x40, add(tr, add(CAPACITY, 128)))
            mstore(tr, 0)
            mstore(add(tr, 0x20), 0)
        }
        header(tr, 1, 0, domainLength);
        bytesFromCalldata(tr, domainOffset, domainLength);
    }

    /// A transcript under a domain tag held in memory.
    function createFromMemory(bytes memory domain) internal pure returns (uint256 tr) {
        return createFromMemorySized(domain, CAPACITY);
    }

    /// A transcript under a domain tag held in memory, with room for `capacity` pending bytes.
    function createFromMemorySized(bytes memory domain, uint256 capacity) internal pure returns (uint256 tr) {
        assembly ("memory-safe") {
            tr := mload(0x40)
            mstore(0x40, add(tr, add(capacity, 128)))
            mstore(tr, 0)
            mstore(add(tr, 0x20), 0)
        }
        header(tr, 1, 0, domain.length);
        assembly ("memory-safe") {
            let len := mload(domain)
            let dst := add(tr, 0x40)
            mcopy(add(dst, 16), add(domain, 0x20), len)
            mstore(add(add(dst, 16), len), 0)
            mstore(add(tr, 0x20), add(16, and(add(len, 15), not(15))))
        }
    }

    /// Appends one raw word.
    function raw(uint256 tr, bytes32 w) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), w)
            mstore(add(tr, 0x20), add(l, 32))
        }
    }

    /// Appends an operation header.
    function header(uint256 tr, uint256 op, uint256 kind, uint256 len) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), shl(128, or(shl(120, op), or(shl(112, kind), len))))
            mstore(add(tr, 0x20), add(l, 16))
        }
    }

    /// Appends `len` calldata bytes, zero-padded to a multiple of sixteen, copied in pieces of at
    /// most `COPY` bytes.
    function bytesFromCalldata(uint256 tr, uint256 offset, uint256 len) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            for { let done := 0 } lt(done, len) { done := add(done, COPY) } {
                let part := sub(len, done)
                if gt(part, COPY) { part := COPY }
                calldatacopy(add(dst, done), add(offset, done), part)
            }
            mstore(add(dst, len), 0)
            mstore(add(tr, 0x20), add(l, and(add(len, 15), not(15))))
        }
    }

    /// Appends a precomputed label: up to two words of header and padded bytes.
    function label(uint256 tr, uint256 w0, uint256 w1, uint256 len) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            mstore(dst, w0)
            mstore(add(dst, 0x20), w1)
            mstore(add(tr, 0x20), add(l, len))
        }
    }

    /// Observes one field element.
    function observe(uint256 tr, uint256 v) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), or(shl(128, 0x03010000000000000000000000000001), v))
            mstore(add(tr, 0x20), add(l, 32))
        }
    }

    /// Observes a slice of `n` field elements stored big-endian, sixteen bytes each, in calldata,
    /// copied in pieces of at most `COPY` bytes.
    function observeSliceFromCalldata(uint256 tr, uint256 offset, uint256 n) internal pure {
        header(tr, 3, 2, n);
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let len := mul(n, 16)
            let dst := add(add(tr, 0x40), l)
            for { let done := 0 } lt(done, len) { done := add(done, COPY) } {
                let part := sub(len, done)
                if gt(part, COPY) { part := COPY }
                calldatacopy(add(dst, done), add(offset, done), part)
            }
            mstore(add(tr, 0x20), add(l, len))
        }
    }

    /// Observes an extension element read from calldata, as the slice of its two coordinates.
    function observeF256FromCalldata(uint256 tr, uint256 offset) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            let v := calldataload(offset)
            mstore(dst, shl(128, 0x03020000000000000000000000000002))
            mstore(add(dst, 16), shl(128, and(v, M128)))
            mstore(add(dst, 32), v)
            mstore(add(tr, 0x20), add(l, 48))
        }
    }

    /// Observes a slice of field elements held in a memory array.
    function observeSlice(uint256 tr, uint256[] memory v) internal pure {
        header(tr, 3, 2, v.length);
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            let n := mload(v)
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                mstore(add(dst, mul(i, 16)), shl(128, mload(add(v, mul(add(i, 1), 0x20)))))
            }
            mstore(add(tr, 0x20), add(l, mul(n, 16)))
        }
    }

    /// Folds the pending bytes into the chaining value and returns it.
    function fold(uint256 tr) internal pure returns (uint256 h) {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let p := add(tr, 0x20)
            mstore(p, mload(tr))
            h := keccak256(p, add(l, 0x20))
            mstore(tr, h)
            mstore(add(tr, 0x20), 0)
        }
    }

    /// One challenge.
    function sample(uint256 tr) internal pure returns (uint256 v) {
        header(tr, 4, 1, 1);
        uint256 h = fold(tr);
        assembly ("memory-safe") {
            mstore(0, h)
            mstore(0x20, 0)
            v := shr(128, keccak256(0, 40))
        }
    }

    /// `n` challenges.
    function sampleVec(uint256 tr, uint256 n) internal pure returns (uint256[] memory v) {
        header(tr, 4, 2, n);
        uint256 h = fold(tr);
        v = new uint256[](n);
        assembly ("memory-safe") {
            for { let j := 0 } lt(mul(j, 2), n) { j := add(j, 1) } {
                mstore(0, h)
                mstore(0x20, shl(192, j))
                let b := keccak256(0, 40)
                mstore(add(v, mul(add(mul(j, 2), 1), 0x20)), shr(128, b))
                if lt(add(mul(j, 2), 1), n) {
                    mstore(add(v, mul(add(mul(j, 2), 2), 0x20)), and(b, M128))
                }
            }
        }
    }

    /// Checks a proof of work over `bits` bits and absorbs its nonce.
    function pow(uint256 tr, uint256 nonce, uint256 bits) internal pure {
        uint256 h = fold(tr);
        bool ok;
        assembly ("memory-safe") {
            switch bits
            case 0 {
                ok := iszero(nonce)
            }
            default {
                mstore(0, h)
                mstore(0x20, or(shl(192, nonce), shl(128, bits)))
                ok := and(iszero(shr(sub(256, bits), keccak256(0, 48))), iszero(gt(bits, 128)))
            }
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            mstore(dst, shl(128, 0x05000000000000000000000000000008))
            mstore(add(dst, 16), shl(192, nonce))
            mstore(add(tr, 0x20), add(l, 32))
        }
        if (!ok) revert ProofOfWork();
    }

    /// A proof of work, then one challenge.
    function powSample(uint256 tr, uint256 nonce, uint256 bits) internal pure returns (uint256) {
        pow(tr, nonce, bits);
        return sample(tr);
    }

    /// A proof of work, then `n` challenges.
    function powSampleVec(uint256 tr, uint256 nonce, uint256 bits, uint256 n) internal pure returns (uint256[] memory) {
        pow(tr, nonce, bits);
        return sampleVec(tr, n);
    }
}
