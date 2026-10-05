// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Arithmetic in GF(2^128) in GHASH form (`x^128 + x^7 + x^2 + x + 1`, low bit the constant term)
/// and in its quadratic extension GF(2^256) (`u^2 + u + x^-1`): a base element in the low 128
/// bits of a word, an extension element as `c1 << 128 | c0`.
///
/// A product of polynomials over GF(2) is taken with the EVM's integer multiplier: each operand
/// is split into five parts holding every fifth bit, so that no column of a partial product sums
/// more than 26 ones and its parity is read off the column's lowest bit.
library F {
    uint256 internal constant M128 = 0xffffffffffffffffffffffffffffffff;
    uint256 internal constant X_INV = 0x80000000000000000000000000000043;
    uint256 internal constant R0 = 0x8421084210842108421084210842108421084210842108421084210842108421;
    uint256 internal constant R1 = 0x0842108421084210842108421084210842108421084210842108421084210842;
    uint256 internal constant R2 = 0x1084210842108421084210842108421084210842108421084210842108421084;
    uint256 internal constant R3 = 0x2108421084210842108421084210842108421084210842108421084210842108;
    uint256 internal constant R4 = 0x4210842108421084210842108421084210842108421084210842108421084210;
    uint256 internal constant M0 = 0x21084210842108421084210842108421;
    uint256 internal constant M1 = 0x42108421084210842108421084210842;
    uint256 internal constant M2 = 0x84210842108421084210842108421084;
    uint256 internal constant M3 = 0x08421084210842108421084210842108;
    uint256 internal constant M4 = 0x10842108421084210842108421084210;

    /// Product of two base elements.
    function mul(uint256 a, uint256 b) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            let a0 := and(a, M0)
            let a1 := and(a, M1)
            let a2 := and(a, M2)
            let a3 := and(a, M3)
            let a4 := and(a, M4)
            let b0 := and(b, M0)
            let b1 := and(b, M1)
            let b2 := and(b, M2)
            let b3 := and(b, M3)
            let b4 := and(b, M4)
            r := and(xor(xor(mul(a0, b0), mul(a1, b4)), xor(xor(mul(a2, b3), mul(a3, b2)), mul(a4, b1))), R0)
            r := xor(r, and(xor(xor(mul(a0, b1), mul(a1, b0)), xor(xor(mul(a2, b4), mul(a3, b3)), mul(a4, b2))), R1))
            r := xor(r, and(xor(xor(mul(a0, b2), mul(a1, b1)), xor(xor(mul(a2, b0), mul(a3, b4)), mul(a4, b3))), R2))
            r := xor(r, and(xor(xor(mul(a0, b3), mul(a1, b2)), xor(xor(mul(a2, b1), mul(a3, b0)), mul(a4, b4))), R3))
            r := xor(r, and(xor(xor(mul(a0, b4), mul(a1, b3)), xor(xor(mul(a2, b2), mul(a3, b1)), mul(a4, b0))), R4))
            let h := shr(128, r)
            r := xor(and(r, M128), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
            h := shr(128, r)
            r := xor(and(r, M128), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
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
            r := xor(and(r, M128), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
            h := shr(128, r)
            r := xor(and(r, M128), xor(xor(h, shl(1, h)), xor(shl(2, h), shl(7, h))))
        }
    }

    /// `a^(2^k)`.
    function frob(uint256 a, uint256 k) internal pure returns (uint256) {
        for (uint256 i = 0; i < k; ++i) {
            a = sq(a);
        }
        return a;
    }

    /// `z · x^-1` for a base element.
    function mulXInv(uint256 z) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := xor(shr(1, z), mul(and(z, 1), X_INV))
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

    /// `Σ a[i] · b[i]` over base elements.
    function dot(uint256[] memory a, uint256[] memory b) internal pure returns (uint256 acc) {
        uint256 n = a.length;
        for (uint256 i = 0; i < n; ++i) {
            acc ^= mul(a[i], b[i]);
        }
    }
}
