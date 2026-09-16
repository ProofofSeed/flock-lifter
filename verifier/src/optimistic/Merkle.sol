// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Fixed-depth Keccak Merkle trees over 32-byte words: a leaf is the word, a node is
/// `keccak(left ‖ right)`, and words past the data are zero.
library Merkle {
    error Proof();

    /// The root of an all-zero tree of depth `depth`.
    function zero(uint256 depth) internal pure returns (bytes32 z) {
        assembly ("memory-safe") {
            for { let k := 0 } lt(k, depth) { k := add(k, 1) } {
                mstore(0, z)
                mstore(0x20, z)
                z := keccak256(0, 0x40)
            }
        }
    }

    /// The roots recomputed from the words `before` and `after` at `[lo, lo + len)` with the
    /// same siblings `proof`, read in order: level by level, parent by parent, left sibling
    /// before right. `before` and `afterw` have the same positive length, and both are
    /// overwritten.
    function roots(uint256[] memory before, uint256[] memory afterw, uint256 lo, uint256 depth, bytes32[] memory proof)
        internal
        pure
        returns (bytes32 rootBefore, bytes32 rootAfter)
    {
        uint256 len = before.length;
        if (len == 0 || afterw.length != len) revert Proof();
        bool used;
        assembly ("memory-safe") {
            // c: [a, b, from, to, cursor, end]
            function child(c, i) -> va, vb {
                let from := mload(add(c, 0x40))
                switch and(iszero(lt(i, from)), lt(i, mload(add(c, 0x60))))
                case 1 {
                    let off := shl(5, sub(i, from))
                    va := mload(add(mload(c), off))
                    vb := mload(add(mload(add(c, 0x20)), off))
                }
                default {
                    let s := mload(add(c, 0x80))
                    if iszero(lt(s, mload(add(c, 0xa0)))) { revert(0, 0) }
                    va := mload(s)
                    vb := va
                    mstore(add(c, 0x80), add(s, 0x20))
                }
            }
            function pair(c, p) {
                let la, lb := child(c, shl(1, p))
                let ra, rb := child(c, add(shl(1, p), 1))
                let out := shl(5, sub(p, shr(1, mload(add(c, 0x40)))))
                mstore(0, la)
                mstore(0x20, ra)
                mstore(add(mload(c), out), keccak256(0, 0x40))
                mstore(0, lb)
                mstore(0x20, rb)
                mstore(add(mload(add(c, 0x20)), out), keccak256(0, 0x40))
            }
            function level(c) {
                let nlo := shr(1, mload(add(c, 0x40)))
                let nhi := shr(1, add(mload(add(c, 0x60)), 1))
                for { let p := nlo } lt(p, nhi) { p := add(p, 1) } {
                    pair(c, p)
                }
                mstore(add(c, 0x40), nlo)
                mstore(add(c, 0x60), nhi)
            }
            let c := mload(0x40)
            mstore(c, add(before, 0x20))
            mstore(add(c, 0x20), add(afterw, 0x20))
            mstore(add(c, 0x40), lo)
            mstore(add(c, 0x60), add(lo, len))
            mstore(add(c, 0x80), add(proof, 0x20))
            mstore(add(c, 0xa0), add(add(proof, 0x20), shl(5, mload(proof))))
            for { let k := 0 } lt(k, depth) { k := add(k, 1) } {
                level(c)
            }
            rootBefore := mload(add(before, 0x20))
            rootAfter := mload(add(afterw, 0x20))
            used := eq(mload(add(c, 0x80)), mload(add(c, 0xa0)))
        }
        if (!used) revert Proof();
    }

    /// The root recomputed from the words `values` at `[lo, lo + len)` and their proof.
    function root(uint256[] memory values, uint256 lo, uint256 depth, bytes32[] memory proof)
        internal
        pure
        returns (bytes32 r)
    {
        uint256[] memory a = new uint256[](values.length);
        uint256[] memory b = new uint256[](values.length);
        for (uint256 i = 0; i < values.length; ++i) {
            a[i] = values[i];
            b[i] = values[i];
        }
        (r,) = roots(a, b, lo, depth, proof);
    }
}
