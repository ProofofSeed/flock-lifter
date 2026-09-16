// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Arithmetic in GF(2^128) in GHASH form (`x^128 + x^7 + x^2 + x + 1`, low bit the constant term)
/// and in its quadratic extension GF(2^256) (`u^2 + u + x^-1`), each element held in one word:
/// a base element in the low 128 bits, an extension element as `c1 << 128 | c0`.
library GF2 {
    uint256 internal constant M128 = 0xffffffffffffffffffffffffffffffff;
    uint256 internal constant X_INV_MASK = 0x80000000000000000000000000000043;

    /// Product of two base elements.
    function mul(uint256 a, uint256 b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            let t := mload(0x40)
            let a2 := shl(1, a)
            let a3 := xor(a2, a)
            let a4 := shl(2, a)
            let a8 := shl(3, a)
            let a12 := xor(a8, a4)
            mstore(t, 0)
            mstore(add(t, 0x20), a)
            mstore(add(t, 0x40), a2)
            mstore(add(t, 0x60), a3)
            mstore(add(t, 0x80), a4)
            mstore(add(t, 0xa0), xor(a4, a))
            mstore(add(t, 0xc0), xor(a4, a2))
            mstore(add(t, 0xe0), xor(a4, a3))
            mstore(add(t, 0x100), a8)
            mstore(add(t, 0x120), xor(a8, a))
            mstore(add(t, 0x140), xor(a8, a2))
            mstore(add(t, 0x160), xor(a8, a3))
            mstore(add(t, 0x180), a12)
            mstore(add(t, 0x1a0), xor(a12, a))
            mstore(add(t, 0x1c0), xor(a12, a2))
            mstore(add(t, 0x1e0), xor(a12, a3))
            r := mload(add(t, shl(5, and(shr(124, b), 15))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(120, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(116, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(112, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(108, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(104, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(100, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(96, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(92, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(88, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(84, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(80, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(76, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(72, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(68, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(64, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(60, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(56, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(52, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(48, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(44, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(40, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(36, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(32, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(28, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(24, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(20, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(16, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(12, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(8, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(shr(4, b), 15)))))
            r := xor(shl(4, r), mload(add(t, shl(5, and(b, 15)))))
            let h := shr(128, r)
            r := xor(and(r, M128), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
            h := shr(128, r)
            r := xor(and(r, M128), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
        }
    }

    /// Square of a base element.
    function sq(uint256 a) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := and(or(a, shl(64, a)), 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff)
            r := and(or(r, shl(32, r)), 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff)
            r := and(or(r, shl(16, r)), 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff)
            r := and(or(r, shl(8, r)), 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff)
            r := and(or(r, shl(4, r)), 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
            r := and(or(r, shl(2, r)), 0x3333333333333333333333333333333333333333333333333333333333333333)
            r := and(or(r, shl(1, r)), 0x5555555555555555555555555555555555555555555555555555555555555555)
            let h := shr(128, r)
            r := xor(and(r, M128), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
            h := shr(128, r)
            r := xor(and(r, M128), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
        }
    }

    /// `a^(2^k)`.
    function frob(uint256 a, uint256 k) internal pure returns (uint256) {
        for (uint256 i = 0; i < k; ++i) {
            a = sq(a);
        }
        return a;
    }

    /// Inverse of a base element, zero for zero, by Itoh-Tsujii: `a^(2^128 − 2)`.
    function inv(uint256 a) internal pure returns (uint256) {
        uint256 x2 = mul(sq(a), a);
        uint256 x3 = mul(sq(x2), a);
        uint256 x6 = mul(frob(x3, 3), x3);
        uint256 x7 = mul(sq(x6), a);
        uint256 x14 = mul(frob(x7, 7), x7);
        uint256 x15 = mul(sq(x14), a);
        uint256 x30 = mul(frob(x15, 15), x15);
        uint256 x31 = mul(sq(x30), a);
        uint256 x62 = mul(frob(x31, 31), x31);
        uint256 x63 = mul(sq(x62), a);
        uint256 x126 = mul(frob(x63, 63), x63);
        uint256 x127 = mul(sq(x126), a);
        return sq(x127);
    }

    /// `z · x^-1` for a base element.
    function mulXInv(uint256 z) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := xor(shr(1, z), mul(and(z, 1), X_INV_MASK))
        }
    }

    /// Product of two extension elements.
    function mul256(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 a0 = a & M128;
        uint256 a1 = a >> 128;
        uint256 b0 = b & M128;
        uint256 b1 = b >> 128;
        uint256 p0 = mul(a0, b0);
        uint256 p1 = mul(a1, b1);
        uint256 p2 = mul(a0 ^ a1, b0 ^ b1);
        return ((p2 ^ p0) << 128) | (p0 ^ mulXInv(p1));
    }

    /// Product of an extension element and a base element.
    function mul256By128(uint256 a, uint256 s) internal pure returns (uint256) {
        return (mul(a >> 128, s) << 128) | mul(a & M128, s);
    }

    /// `u · a` for an extension element.
    function mulU(uint256 a) internal pure returns (uint256) {
        uint256 a0 = a & M128;
        uint256 a1 = a >> 128;
        return ((a0 ^ a1) << 128) | mulXInv(a1);
    }

    /// A fresh zeroed array of `n` words.
    function alloc(uint256 n) internal pure returns (uint256[] memory v) {
        v = new uint256[](n);
    }

    /// The equality table of `point` over base elements, lowest coordinate at the lowest index
    /// bit: `t[i] = Π_j (bit_j(i) ? p_j : 1 + p_j)`.
    function eqTable(uint256[] memory point) internal pure returns (uint256[] memory t) {
        uint256 d = point.length;
        t = new uint256[](1 << d);
        t[0] = 1;
        for (uint256 j = 0; j < d; ++j) {
            uint256 half = 1 << j;
            uint256 p = point[j];
            for (uint256 i = 0; i < half; ++i) {
                uint256 lo = t[i];
                uint256 hi = mul(lo, p);
                t[i + half] = hi;
                t[i] = lo ^ hi;
            }
        }
    }

    /// The equality table of `point` over extension elements, lowest coordinate first.
    function eqTable256(uint256[] memory point) internal pure returns (uint256[] memory t) {
        uint256 d = point.length;
        t = new uint256[](1 << d);
        t[0] = 1;
        for (uint256 j = 0; j < d; ++j) {
            uint256 half = 1 << j;
            uint256 p = point[j];
            for (uint256 i = 0; i < half; ++i) {
                uint256 lo = t[i];
                uint256 hi = mul256(lo, p);
                t[i + half] = hi;
                t[i] = lo ^ hi;
            }
        }
    }

    /// `Σ a[i] · b[i]` over base elements.
    function dot(uint256[] memory a, uint256[] memory b) internal pure returns (uint256 acc) {
        uint256 n = a.length;
        for (uint256 i = 0; i < n; ++i) {
            acc ^= mul(a[i], b[i]);
        }
    }

    /// A base element in Flock's native layout — `lo` then `hi`, each little-endian — read as the
    /// big-endian 16-byte integer `x`, converted to its value.
    function fromNative(uint256 x) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := or(
                and(shr(8, x), 0x00ff00ff00ff00ff00ff00ff00ff00ff),
                shl(8, and(x, 0x00ff00ff00ff00ff00ff00ff00ff00ff))
            )
            v := or(
                and(shr(16, v), 0x0000ffff0000ffff0000ffff0000ffff),
                shl(16, and(v, 0x0000ffff0000ffff0000ffff0000ffff))
            )
            v := or(
                and(shr(32, v), 0x00000000ffffffff00000000ffffffff),
                shl(32, and(v, 0x00000000ffffffff00000000ffffffff))
            )
            v := or(shr(64, v), shl(64, and(v, 0xffffffffffffffff)))
        }
    }
}
