// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "../GF2.sol";
import {Tables} from "../Tables.sol";

/// The ring-switching basis evaluation of Flock (`eval_rs_eq_prefix_f256` and
/// `eval_rs_eq_finish_from_prefix_binary_q_f256`), over the tensor algebra
/// `GF(2^256) ⊗ GF(2^128)` held as two 128-element coefficient vectors `c0` and `c1`: element `i`
/// of a vector is the right-hand coefficient of `x^i` on the left.
///
/// Left multiplication by a base element combines the rows by the rows of its multiplication
/// matrix, which a linear recurrence gives in 128 steps; right multiplication multiplies every
/// row by the same element. Both are table lookups, so no bit matrix is ever transposed.
library Tensor {
    /// Scratch space: four table regions and four row buffers.
    struct Work {
        uint256 tabA;
        uint256 tabB;
        uint256 tabF;
        uint256 tabL;
        uint256 m0;
        uint256 m1;
        uint256 n0;
        uint256 n1;
    }

    function work() internal pure returns (Work memory w) {
        w.tabA = Tables.region();
        w.tabB = Tables.region();
        w.tabF = Tables.region();
        w.tabL = Tables.region();
        w.m0 = _buffer();
        w.m1 = _buffer();
        w.n0 = _buffer();
        w.n1 = _buffer();
    }

    function _buffer() private pure returns (uint256 b) {
        assembly ("memory-safe") {
            b := mload(0x40)
            mstore(0x40, add(b, 0x1000))
        }
    }

    function _data(uint256[] memory v) private pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(v, 0x20)
        }
    }

    /// The prefix tensor `Π_i (1 ⊗ (1 + z_i) + q_i ⊗ 1)`, with `z_i = z[zFrom + i]`.
    function prefix(uint256[] memory z, uint256 zFrom, uint256[] memory q, Work memory w)
        internal
        pure
        returns (uint256[] memory c0, uint256[] memory c1)
    {
        c0 = new uint256[](128);
        c1 = new uint256[](128);
        c0[0] = 1;
        uint256 p0 = _data(c0);
        uint256 p1 = _data(c1);
        for (uint256 i = 0; i < q.length; ++i) {
            _horizontal(p0, p1, q[i], w);
            Tables.buildMul(w.tabF, 1 ^ z[zFrom + i]);
            uint256 tabF = w.tabF;
            uint256 n0 = w.n0;
            uint256 n1 = w.n1;
            for (uint256 k = 0; k < 128; ++k) {
                uint256 at = k << 5;
                uint256 a;
                uint256 b;
                uint256 x0;
                uint256 x1;
                assembly ("memory-safe") {
                    a := mload(add(p0, at))
                    b := mload(add(p1, at))
                    x0 := mload(add(n0, at))
                    x1 := mload(add(n1, at))
                }
                a = Tables.lookup(tabF, a) ^ x0;
                b = Tables.lookup(tabF, b) ^ x1;
                assembly ("memory-safe") {
                    mstore(add(p0, at), a)
                    mstore(add(p1, at), b)
                }
            }
        }
    }

    /// Writes `(q ⊗ 1)·(c0 + u·c1)` to `w.n0`, `w.n1`, by schoolbook over `u² = u + x^-1`:
    /// `c0' = q0·c0 + x^-1·q1·c1` and `c1' = (q0 + q1)·c1 + q1·c0`.
    function _horizontal(uint256 p0, uint256 p1, uint256 q, Work memory w) private pure {
        Tables.masks(q & GF2.M128, w.m0);
        Tables.masks(q >> 128, w.m1);
        Tables.build(w.tabA, p0);
        Tables.build(w.tabB, p1);
        uint256 tabA = w.tabA;
        uint256 tabB = w.tabB;
        uint256 m0 = w.m0;
        uint256 m1 = w.m1;
        uint256 n0 = w.n0;
        uint256 n1 = w.n1;
        for (uint256 k = 0; k < 128; ++k) {
            uint256 at = k << 5;
            uint256 mask0;
            uint256 mask1;
            assembly ("memory-safe") {
                mask0 := mload(add(m0, at))
                mask1 := mload(add(m1, at))
            }
            uint256 a0 = Tables.lookup(tabA, mask0);
            uint256 b1 = Tables.lookup(tabB, mask1);
            uint256 x1 = Tables.lookup(tabB, mask0 ^ mask1) ^ Tables.lookup(tabA, mask1);
            assembly ("memory-safe") {
                mstore(add(n0, at), a0)
                mstore(add(m0, at), b1)
                mstore(add(n1, at), x1)
            }
        }
        assembly ("memory-safe") {
            let first := mload(m0)
            for { let k := 0 } lt(k, 127) { k := add(k, 1) } {
                let slot := add(n0, shl(5, k))
                mstore(slot, xor(mload(slot), mload(add(m0, shl(5, add(k, 1))))))
            }
            for { let j := 0 } lt(j, 4) { j := add(j, 1) } {
                let k := byte(j, 0x0001067f00000000000000000000000000000000000000000000000000000000)
                let slot := add(n0, shl(5, k))
                mstore(slot, xor(mload(slot), first))
            }
        }
    }

    /// Prepares `w.tabL` for folds against the coefficients `coeffs`.
    function foldTable(uint256[] memory coeffs, Work memory w) internal pure {
        Tables.build(w.tabL, _data(coeffs));
    }

    /// `Σ_i x^i · L(v[i]·s)` with `L` the map of `w.tabL` and `w.tabF` the table of `s`.
    function _fold(uint256 v, Work memory w) private pure returns (uint256 acc) {
        uint256 tabF = w.tabF;
        uint256 tabL = w.tabL;
        for (uint256 i = 128; i > 0; --i) {
            uint256 e;
            assembly ("memory-safe") {
                e := mload(add(v, shl(5, sub(i, 1))))
            }
            uint256 l = Tables.lookup(tabL, Tables.lookup(tabF, e));
            acc = ((acc << 1) & GF2.M128) ^ ((acc >> 127) * 0x87) ^ l;
        }
    }

    /// The finished evaluation at binary suffix `y`, as an extension element, against the
    /// coefficients prepared by `foldTable`.
    function finish(
        uint256[] memory c0,
        uint256[] memory c1,
        uint256[] memory zSuffix,
        uint256 zFrom,
        uint256 y,
        Work memory w
    ) internal pure returns (uint256) {
        uint256 s = 1;
        uint256 n = zSuffix.length - zFrom;
        for (uint256 j = 0; j < n; ++j) {
            uint256 zj = zSuffix[zFrom + j];
            s = GF2.mul(s, (y >> j) & 1 == 1 ? zj : 1 ^ zj);
        }
        Tables.buildMul(w.tabF, s);
        return (_fold(_data(c1), w) << 128) | _fold(_data(c0), w);
    }
}
