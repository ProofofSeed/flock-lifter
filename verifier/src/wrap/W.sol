// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "../Constants.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
import {K} from "./K.sol";

/// What the wrap verifier's stages share: transcript forks and extension-field operations on top
/// of `Transcript`, and small kernels over vectors of field elements.
library W {
    uint256 internal constant M128 = 0xffffffffffffffffffffffffffffffff;

    /// Emitted at the end of stage `id` with the gas left, the transcript's state, which is its
    /// chaining value with the pending bytes folded in, and the free memory pointer.
    event Stage(uint256 indexed id, uint256 gasLeft, bytes32 state, uint256 memoryTop);

    function mark(uint256 id, uint256 tr) internal {
        emit Stage(id, gasleft(), state(tr), top());
    }

    /// The chaining value `tr` would have were its pending bytes folded in.
    function state(uint256 tr) internal pure returns (bytes32 s) {
        assembly ("memory-safe") {
            let p := add(tr, 0x20)
            let l := mload(p)
            mstore(p, mload(tr))
            s := keccak256(p, add(l, 0x20))
            mstore(p, l)
        }
    }

    /// The free memory pointer.
    function top() internal pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := mload(0x40)
        }
    }

    /// Frees every allocation made since `top` returned `p`; none may be used afterwards.
    function release(uint256 p) internal pure {
        assembly ("memory-safe") {
            mstore(0x40, p)
        }
    }

    /// Appends bytes that are whole transcript operations.
    function append(uint256 tr, bytes memory ops) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let n := mload(ops)
            mcopy(add(add(tr, 0x40), l), add(ops, 0x20), n)
            mstore(add(tr, 0x20), add(l, n))
        }
    }

    /// Appends `len` bytes of calldata as they are.
    function appendCalldata(uint256 tr, uint256 at, uint256 len) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            calldatacopy(add(add(tr, 0x40), l), at, len)
            mstore(add(tr, 0x20), add(l, len))
        }
    }

    /// Observes `n` field elements held in memory at `at`, a word each.
    function observeWords(uint256 tr, uint256 at, uint256 n) internal pure {
        Transcript.header(tr, 3, 2, n);
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                mstore(add(dst, shl(4, i)), shl(128, mload(add(at, shl(5, i)))))
            }
            mstore(add(tr, 0x20), add(l, shl(4, n)))
        }
    }

    /// A transcript under `domain`, seeded with two challenges of `tr`.
    function fork(uint256 tr, bytes memory domain, uint256 capacity) internal pure returns (uint256 child) {
        uint256 s0 = Transcript.sample(tr);
        uint256 s1 = Transcript.sample(tr);
        child = Transcript.createFromMemorySized(domain, capacity);
        Transcript.observe(child, s0);
        Transcript.observe(child, s1);
    }

    /// Closes the fork `child` of `tr`: two of its challenges are observed by `tr`.
    function merge(uint256 tr, uint256 child) internal pure {
        uint256 d0 = Transcript.sample(child);
        uint256 d1 = Transcript.sample(child);
        Transcript.observe(tr, d0);
        Transcript.observe(tr, d1);
    }

    /// One extension-field challenge.
    function sample256(uint256 tr) internal pure returns (uint256 v) {
        Transcript.header(tr, 4, 2, 2);
        uint256 h = Transcript.fold(tr);
        assembly ("memory-safe") {
            mstore(0, h)
            mstore(0x20, 0)
            let b := keccak256(0, 40)
            v := or(shl(128, b), shr(128, b))
        }
    }

    /// Observes an extension element.
    function observe256(uint256 tr, uint256 v) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            mstore(dst, shl(128, 0x03020000000000000000000000000002))
            mstore(add(dst, 16), shl(128, v))
            mstore(add(dst, 32), v)
            mstore(add(tr, 0x20), add(l, 48))
        }
    }

    /// The equality table of `point[from .. from + n)`, lowest coordinate at the lowest index bit,
    /// scaled by `seed`.
    function eqTable(uint256[] memory point, uint256 from, uint256 n, uint256 seed) internal pure returns (uint256[] memory t) {
        t = new uint256[](1 << n);
        K.eqTable(ptr(t), ptr(point) + 32 * from, n, seed);
    }

    /// Where the entries of `v` sit in memory.
    function ptr(uint256[] memory v) internal pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(v, 0x20)
        }
    }

    /// Where the bytes of `b` sit in memory.
    function data(bytes memory b) internal pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(b, 0x20)
        }
    }

    /// `Π_j eq(point[from + j], bit_j(bits))` over `n` coordinates.
    function eqWeight(uint256[] memory point, uint256 from, uint256 n, uint256 bits) internal pure returns (uint256 acc) {
        acc = 1;
        for (uint256 j = 0; j < n; ++j) {
            uint256 x = point[from + j];
            acc = F.mul(acc, (bits >> j) & 1 == 1 ? x : x ^ 1);
        }
    }

    /// `Σ_{i<count} eq(point[from .. from + n), i)`.
    function prefixSum(uint256[] memory point, uint256 from, uint256 n, uint256 count) internal pure returns (uint256 acc) {
        if (count >= 1 << n) return 1;
        uint256 run = 1;
        for (uint256 j = n; j > 0; --j) {
            uint256 x = point[from + j - 1];
            if ((count >> (j - 1)) & 1 == 1) {
                acc ^= F.mul(run, x ^ 1);
                run = F.mul(run, x);
            } else {
                run = F.mul(run, x ^ 1);
            }
        }
    }

    /// A quadratic round's claim at `r`, from the message `(g(1), g(∞))` and the previous claim.
    function quadratic(uint256 claim, uint256 e1, uint256 einf, uint256 r) internal pure returns (uint256) {
        return F.mul(einf, F.sq(r)) ^ F.mul(claim ^ einf, r) ^ claim ^ e1;
    }

    /// `(w, total)` with `w[i] = Π_{j≠i} (z + node_j)` and `total = Π_j (z + node_j)` over the 64
    /// φ₈ nodes starting at `base`.
    function leaveOneOut(bytes memory phi, uint256 base, uint256 z) internal pure returns (uint256[] memory w, uint256 total) {
        uint256[] memory diff = new uint256[](64);
        uint256[] memory pre = new uint256[](65);
        pre[0] = 1;
        for (uint256 i = 0; i < 64; ++i) {
            diff[i] = z ^ Constants.at(phi, base + i);
            pre[i + 1] = F.mul(pre[i], diff[i]);
        }
        total = pre[64];
        w = new uint256[](64);
        uint256 suf = 1;
        for (uint256 i = 64; i > 0; --i) {
            w[i - 1] = F.mul(pre[i - 1], suf);
            suf = F.mul(suf, diff[i - 1]);
        }
    }

    /// The Lagrange weights of the subspace `φ₈(0..64)` at `z`.
    function lagrange(bytes memory phi, uint256 z) internal pure returns (uint256[] memory w) {
        (w,) = leaveOneOut(phi, 0, z);
        for (uint256 i = 0; i < 64; ++i) {
            w[i] = F.mul(w[i], Constants.DEN6_INV);
        }
    }

    /// Entry `i` of a table of big-endian values of `width` bytes each, `width` at most 32.
    function entry(bytes memory table, uint256 i, uint256 width) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(sub(256, shl(3, width)), mload(add(add(table, 32), mul(i, width))))
        }
    }

    /// The big-endian value of the `width` bytes of `table` at byte `at`, `width` at most 32.
    function read(bytes memory table, uint256 at, uint256 width) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(sub(256, shl(3, width)), mload(add(add(table, 32), at)))
        }
    }
}
