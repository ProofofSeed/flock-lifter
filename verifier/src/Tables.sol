// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Table-driven GF(2)-linear kernels over 128-bit words, in memory regions of 4096 words.
///
/// A combination table of 128 values `v` holds, for each of 16 byte positions `g` and each byte
/// `b`, the XOR of the `v[8g + t]` over the set bits `t` of `b`; looking up the 16 bytes of a mask
/// then XORs the values its set bits select. With `v[j] = a·x^j` that is multiplication by `a`,
/// and with `v` the rows of a tensor it is the rows' combination by one row of a matrix.
library Tables {
    uint256 internal constant WORDS = 4096;
    uint256 internal constant M128 = 0xffffffffffffffffffffffffffffffff;

    /// A fresh table region.
    function region() internal pure returns (uint256 tab) {
        assembly ("memory-safe") {
            tab := mload(0x40)
            mstore(0x40, add(tab, mul(WORDS, 0x20)))
        }
    }

    /// Fills `tab` with the combination table of the 128 values at memory `values`.
    function build(uint256 tab, uint256 values) internal pure {
        assembly ("memory-safe") {
            for { let g := 0 } lt(g, 16) { g := add(g, 1) } {
                let base := add(tab, shl(13, g))
                mstore(base, 0)
                for { let t := 0 } lt(t, 8) { t := add(t, 1) } {
                    let v := mload(add(values, shl(5, add(shl(3, g), t))))
                    let half := shl(t, 1)
                    for { let b := 0 } lt(b, half) { b := add(b, 1) } {
                        mstore(add(base, shl(5, add(half, b))), xor(mload(add(base, shl(5, b))), v))
                    }
                }
            }
        }
    }

    /// Fills `tab` with the multiplication table of `a`.
    function buildMul(uint256 tab, uint256 a) internal pure {
        uint256 values;
        assembly ("memory-safe") {
            values := mload(0x40)
            let v := a
            for { let j := 0 } lt(j, 128) { j := add(j, 1) } {
                mstore(add(values, shl(5, j)), v)
                v := xor(and(shl(1, v), M128), mul(shr(127, v), 0x87))
            }
            mstore(0x40, add(values, 0x1000))
        }
        build(tab, values);
        assembly ("memory-safe") {
            mstore(0x40, values)
        }
    }

    /// The combination of `tab`'s values selected by the set bits of `mask`.
    function lookup(uint256 tab, uint256 mask) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := mload(add(tab, shl(5, and(mask, 0xff))))
            r := xor(r, mload(add(tab, shl(5, add(256, and(shr(8, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(512, and(shr(16, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(768, and(shr(24, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(1024, and(shr(32, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(1280, and(shr(40, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(1536, and(shr(48, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(1792, and(shr(56, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(2048, and(shr(64, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(2304, and(shr(72, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(2560, and(shr(80, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(2816, and(shr(88, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(3072, and(shr(96, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(3328, and(shr(104, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(3584, and(shr(112, mask), 0xff))))))
            r := xor(r, mload(add(tab, shl(5, add(3840, and(shr(120, mask), 0xff))))))
        }
    }

    /// The 128-bit bit reversal of `q`.
    function reverse(uint256 q) internal pure returns (uint256 r) {
        assembly ("memory-safe") {
            r := or(shl(1, and(q, 0x55555555555555555555555555555555)), and(shr(1, q), 0x55555555555555555555555555555555))
            r := or(shl(2, and(r, 0x33333333333333333333333333333333)), and(shr(2, r), 0x33333333333333333333333333333333))
            r := or(shl(4, and(r, 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)), and(shr(4, r), 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f))
            r := or(shl(8, and(r, 0x00ff00ff00ff00ff00ff00ff00ff00ff)), and(shr(8, r), 0x00ff00ff00ff00ff00ff00ff00ff00ff))
            r := or(shl(16, and(r, 0x0000ffff0000ffff0000ffff0000ffff)), and(shr(16, r), 0x0000ffff0000ffff0000ffff0000ffff))
            r := or(shl(32, and(r, 0x00000000ffffffff00000000ffffffff)), and(shr(32, r), 0x00000000ffffffff00000000ffffffff))
            r := or(shl(64, and(r, 0xffffffffffffffff)), shr(64, r))
        }
    }

    /// The 128 rows of the matrix of multiplication by `q`, written at memory `out`: bit `j` of row
    /// `k` is bit `k` of `x^j·q`.
    function masks(uint256 q, uint256 out) internal pure {
        uint256 rev = reverse(q);
        assembly ("memory-safe") {
            let low := and(rev, 0x7f)
            let m127 := xor(rev, xor(shl(121, low), xor(shl(126, and(low, 3)), shl(127, and(low, 1)))))
            let s := and(shl(1, m127), M128)
            let prev := 0
            for { let k := 0 } lt(k, 128) { k := add(k, 1) } {
                let m := xor(and(shl(1, prev), M128), and(shr(k, q), 1))
                if or(lt(k, 3), eq(k, 7)) { m := xor(m, s) }
                mstore(add(out, shl(5, k)), m)
                prev := m
            }
        }
    }
}
