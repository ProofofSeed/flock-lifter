// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "./GF2.sol";

/// The ring-switching basis evaluation of Flock (`eval_rs_eq_prefix_f256` and
/// `eval_rs_eq_finish_from_prefix_binary_q_f256`), over the tensor algebra
/// `GF(2^256) ⊗ GF(2^128)` held as two 128-element coefficient vectors `c0` and `c1`: element `i`
/// of a vector is the right-hand coefficient of `x^i` on the left.
library Tensor {
    /// `dst[j] = Σ_i bit_j(src[i])·x^i`: the transpose of a 128×128 bit matrix, a byte of every
    /// row at a time through `spread`, which puts bit `t` of a byte at bit `32·t`.
    function transpose(uint256[] memory src, bytes memory spread) internal pure returns (uint256[] memory dst) {
        dst = new uint256[](128);
        assembly ("memory-safe") {
            let s := add(src, 0x20)
            let d := add(dst, 0x20)
            let tab := add(spread, 0x20)
            for { let byteAt := 0 } lt(byteAt, 128) { byteAt := add(byteAt, 8) } {
                for { let c := 0 } lt(c, 128) { c := add(c, 32) } {
                    let acc := 0
                    for { let t := 0 } lt(t, 32) { t := add(t, 1) } {
                        let b := and(shr(byteAt, mload(add(s, shl(5, add(c, t))))), 0xff)
                        acc := or(acc, shl(t, mload(add(tab, shl(5, b)))))
                    }
                    for { let k := 0 } lt(k, 8) { k := add(k, 1) } {
                        let slot := add(d, shl(5, add(byteAt, k)))
                        mstore(slot, or(mload(slot), shl(c, and(shr(shl(5, k), acc), 0xffffffff))))
                    }
                }
            }
        }
    }

    /// `v[i]·s` for every entry.
    function scale(uint256[] memory v, uint256 s) internal pure returns (uint256[] memory out) {
        out = new uint256[](128);
        for (uint256 i = 0; i < 128; ++i) {
            out[i] = GF2.mul(v[i], s);
        }
    }

    /// The prefix tensor `Π_i (1 ⊗ (1 + z_i) + q_i ⊗ 1)`.
    function prefix(uint256[] memory z, uint256 zFrom, uint256[] memory q, bytes memory spread)
        internal
        pure
        returns (uint256[] memory c0, uint256[] memory c1)
    {
        c0 = new uint256[](128);
        c1 = new uint256[](128);
        c0[0] = 1;
        for (uint256 i = 0; i < q.length; ++i) {
            (uint256[] memory h0, uint256[] memory h1) = horizontal(c0, c1, q[i], spread);
            uint256 a = 1 ^ z[zFrom + i];
            for (uint256 k = 0; k < 128; ++k) {
                c0[k] = GF2.mul(c0[k], a) ^ h0[k];
                c1[k] = GF2.mul(c1[k], a) ^ h1[k];
            }
        }
    }

    /// `(q ⊗ 1)·(c0 + u·c1)` for an extension element `q`, by Karatsuba over `u² = u + x^-1`,
    /// every horizontal scaling done in the transposed domain.
    function horizontal(uint256[] memory c0, uint256[] memory c1, uint256 q, bytes memory spread)
        internal
        pure
        returns (uint256[] memory h0, uint256[] memory h1)
    {
        uint256 q0 = q & GF2.M128;
        uint256 q1 = q >> 128;
        uint256[] memory t0 = transpose(c0, spread);
        uint256[] memory t1 = transpose(c1, spread);
        for (uint256 k = 0; k < 128; ++k) {
            uint256 a = t0[k];
            uint256 b = t1[k];
            uint256 p0 = GF2.mul(a, q0);
            t0[k] = p0 ^ GF2.mulXInv(GF2.mul(b, q1));
            t1[k] = GF2.mul(a ^ b, q0 ^ q1) ^ p0;
        }
        h0 = transpose(t0, spread);
        h1 = transpose(t1, spread);
    }

    /// The nibble tables of `e ↦ Σ_j bit_j(e)·coeffs[j]`.
    function foldTable(uint256[] memory coeffs) internal pure returns (uint256[] memory t) {
        t = new uint256[](32 * 16);
        for (uint256 k = 0; k < 32; ++k) {
            uint256 base = 16 * k;
            for (uint256 n = 1; n < 16; ++n) {
                uint256 low = n & (~n + 1);
                uint256 bit = low == 1 ? 0 : low == 2 ? 1 : low == 4 ? 2 : 3;
                t[base + n] = t[base + (n ^ low)] ^ coeffs[4 * k + bit];
            }
        }
    }

    /// `Σ_i x^i · L(v[i]·s)`, `L` the map of `table`: Flock's `fold_vertical` of the vector
    /// scaled by `s`.
    function foldScaled(uint256[] memory v, uint256 s, uint256[] memory table) internal pure returns (uint256 acc) {
        for (uint256 i = 128; i > 0; --i) {
            uint256 e = GF2.mul(v[i - 1], s);
            uint256 l;
            assembly ("memory-safe") {
                let base := add(table, 0x20)
                for { let k := 0 } lt(k, 32) { k := add(k, 1) } {
                    let n := and(shr(mul(k, 4), e), 15)
                    l := xor(l, mload(add(base, shl(5, add(mul(k, 16), n)))))
                }
                let top := shr(127, acc)
                acc := xor(and(shl(1, acc), 0xffffffffffffffffffffffffffffffff), mul(top, 0x87))
            }
            acc ^= l;
        }
    }

    /// The finished evaluation at binary suffix `y`, as an extension element.
    function finish(
        uint256[] memory c0,
        uint256[] memory c1,
        uint256[] memory zSuffix,
        uint256 zFrom,
        uint256 y,
        uint256[] memory table
    ) internal pure returns (uint256) {
        uint256 s = 1;
        uint256 n = zSuffix.length - zFrom;
        for (uint256 j = 0; j < n; ++j) {
            uint256 zj = zSuffix[zFrom + j];
            s = GF2.mul(s, (y >> j) & 1 == 1 ? zj : 1 ^ zj);
        }
        return (foldScaled(c1, s, table) << 128) | foldScaled(c0, s, table);
    }
}
