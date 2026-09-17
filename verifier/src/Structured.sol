// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "./Constants.sol";
import {GF2} from "./GF2.sol";

/// The structured part of a lincheck matrix claim — the Keccak-f sub-blocks and the constant-wire
/// pin — paired with the claim's collapsed witness, from the shared fold's rotation-invariant form
/// (see `Program::structured_value` and `keccak::fold_shared_paired`).
library Structured {
    /// Words of an 8-bit multiplication table.
    uint256 internal constant TAB8 = 256 * 32;

    /// The claim's inputs, and the geometry of its block.
    struct Input {
        uint256 alpha;
        uint256 beta;
        uint256[] skip;
        uint256[] z;
        uint256[] x;
        uint256[] r;
        uint256 first;
        uint256 subs;
    }

    /// Buffers one claim's evaluation works in, reusable across claims and left unwritten until
    /// used: a pointer list to the tables (pairing weights, a scratch table, alpha, skip weights),
    /// the kernel, the round map's scratch, the two `eq` tables and the constant tables. The tables
    /// come last, so that a caller done with them may reuse their memory.
    function work() internal pure returns (uint256[] memory ctxArr) {
        ctxArr = new uint256[](13);
        bytes memory pre = Constants.PREIMAGE0;
        bytes memory rho = Constants.RHO;
        bytes memory rcs = Constants.ROUND_CONSTANT_BITS;
        assembly ("memory-safe") {
            let cx := add(ctxArr, 0x20)
            let at := mload(0x40)
            mstore(add(cx, 0x20), at)
            at := add(at, shl(5, 1600))
            mstore(add(cx, 0x40), at)
            at := add(at, shl(5, 2240))
            mstore(add(cx, 0x60), at)
            at := add(at, shl(5, 1024))
            mstore(add(cx, 0x80), at)
            at := add(at, shl(5, 1024))
            mstore(add(cx, 0x180), at)
            at := add(at, shl(5, 64))
            mstore(cx, at)
            mstore(0x40, add(at, add(mul(TAB8, 66), shl(9, 64))))
            mstore(add(cx, 0xa0), add(pre, 0x20))
            mstore(add(cx, 0xc0), add(rho, 0x20))
            mstore(add(cx, 0xe0), add(rcs, 0x20))
        }
    }

    /// The structured part of claim `c`, paired with its collapsed witness, computed in `ctxArr`
    /// from [`work`].
    function value(Input memory c, uint256[] memory ctxArr) internal pure returns (uint256) {
        bind(c, ctxArr);
        (uint256 v, uint256 rc, uint256 weights, uint256 pins, uint256 col0) = _run(ctxArr, c.alpha, 0, 0, 24);
        return combine(c, v, rc, weights, pins, col0);
    }

    /// Points the buffers of `ctxArr` at claim `c`'s inputs.
    function bind(Input memory c, uint256[] memory ctxArr) internal pure {
        assembly ("memory-safe") {
            let cx := add(ctxArr, 0x20)
            mstore(add(cx, 0x100), add(mload(add(c, 0x40)), 0x20))
            mstore(add(cx, 0x120), add(mload(add(c, 0x60)), 0x20))
            mstore(add(cx, 0x140), add(mload(add(c, 0x80)), 0x20))
            mstore(add(cx, 0x160), add(mload(add(c, 0xa0)), 0x20))
        }
    }

    /// Computes the pairing weights into the pairs buffer, starts the kernel in the kernel buffer
    /// and returns the output pins' weight sum.
    function setup(Input memory c, uint256[] memory ctxArr) internal pure returns (uint256 pins) {
        bind(c, ctxArr);
        (,,, pins,) = _run(ctxArr, c.alpha, 1, 0, 0);
    }

    /// Folds rounds `from..to` (in fold order) of the kernel held in the kernel buffer, with the
    /// pairing weights read from the pairs buffer.
    function rounds(Input memory c, uint256[] memory ctxArr, uint256 from, uint256 to)
        internal
        pure
        returns (uint256 v, uint256 rc, uint256 weights)
    {
        bind(c, ctxArr);
        (v, rc, weights,,) = _run(ctxArr, c.alpha, 2, from, to);
    }

    /// The last pairing of the fold and the column `eq` weight of word 0, with the pairing
    /// weights read from the pairs buffer.
    function last(Input memory c, uint256[] memory ctxArr) internal pure returns (uint256 v, uint256 col0) {
        bind(c, ctxArr);
        (v,,,, col0) = _run(ctxArr, c.alpha, 3, 0, 0);
    }

    /// The structured value from the fold's accumulators.
    function combine(Input memory c, uint256 v, uint256 rc, uint256 weights, uint256 pins, uint256 col0)
        internal
        pure
        returns (uint256)
    {
        uint256 konst = _konst(c, rc, weights, pins);
        uint256 weight = _rangeSum(c.x, c.r, true, c.first, c.first + c.subs);
        uint256 weightKonst = _rangeSum(c.x, c.r, false, c.first, c.first + c.subs);
        uint256 eqConst = col0;
        for (uint256 i = 10; i < c.r.length; ++i) {
            eqConst = GF2.mul(eqConst, 1 ^ c.r[i]);
        }
        return GF2.mul(weight, v) ^ GF2.mul(GF2.mul(c.z[0], eqConst), GF2.mul(weightKonst, konst) ^ c.beta);
    }

    /// The constant-wire part of the fold.
    function _konst(Input memory c, uint256 rc, uint256 weights, uint256 pins) private pure returns (uint256) {
        uint256 skipSum;
        for (uint256 u = 0; u < 64; ++u) {
            skipSum ^= c.skip[u];
        }
        return rc ^ GF2.mul(skipSum, pins ^ GF2.mul(c.alpha, weights));
    }

    /// `Σ_{a ≤ j < b} Π_i g_i(bit i of j)` over the high point coordinates, with
    /// `g_i = ((1 + x_i)(1 + r_i), x_i·r_i)` when `both`, else `(1 + x_i, x_i)`.
    function _rangeSum(uint256[] memory x, uint256[] memory r, bool both, uint256 a, uint256 b)
        private
        pure
        returns (uint256)
    {
        uint256 k = x.length - 10;
        uint256[] memory g0 = new uint256[](k);
        uint256[] memory g1 = new uint256[](k);
        for (uint256 i = 0; i < k; ++i) {
            uint256 xi = x[10 + i];
            if (both) {
                uint256 ri = r[10 + i];
                g0[i] = GF2.mul(1 ^ xi, 1 ^ ri);
                g1[i] = GF2.mul(xi, ri);
            } else {
                g0[i] = 1 ^ xi;
                g1[i] = xi;
            }
        }
        return _prefixSum(g0, g1, b) ^ _prefixSum(g0, g1, a);
    }

    function _prefixSum(uint256[] memory g0, uint256[] memory g1, uint256 n) private pure returns (uint256 acc) {
        uint256 k = g0.length;
        uint256[] memory full = new uint256[](k + 1);
        full[0] = 1;
        for (uint256 i = 0; i < k; ++i) {
            full[i + 1] = GF2.mul(full[i], g0[i] ^ g1[i]);
        }
        if (n == 1 << k) return full[k];
        uint256 high = 1;
        for (uint256 i = k; i > 0; --i) {
            if ((n >> (i - 1)) & 1 == 1) {
                acc ^= GF2.mul(GF2.mul(high, g0[i - 1]), full[i - 1]);
                high = GF2.mul(high, g1[i - 1]);
            } else {
                high = GF2.mul(high, g0[i - 1]);
            }
        }
    }

    /// The rotation-invariant fold over the buffers `ctxArr` points to: the paired value, the
    /// round constants' part, the sums of the χ and output-pin row weights, and the column `eq`
    /// weight of word 0. Mode 0 runs it whole; mode 1 only computes the pairing weights and starts
    /// the kernel; mode 2 folds rounds `fromRound..toRound`; mode 3 makes the last pairing.
    function _run(uint256[] memory ctxArr, uint256 alphaIn, uint256 mode, uint256 fromRound, uint256 toRound)
        private
        pure
        returns (uint256 outValue, uint256 outRc, uint256 outWeights, uint256 outPins, uint256 outCol0)
    {
        assembly ("memory-safe") {
            // ctx: tables, kernel, scratch, row eq, col eq, preimages, rho, round-constant bits,
            // skip, z, x, r, pairs — every pointer to a first element. Table slot d holds the 8-bit
            // table of pair[d], slot 64 a scratch table and slot 65 the 4-bit table of alpha; the
            // 4-bit tables of skip[u] follow, sixteen words each.
            function tbuild8(t, a) {
                mstore(t, 0)
                mstore(add(t, 0x20), a)
                for { let i := 1 } lt(i, 128) { i := add(i, 1) } {
                    let v := shl(1, mload(add(t, shl(5, i))))
                    mstore(add(t, shl(6, i)), v)
                    mstore(add(t, add(shl(6, i), 0x20)), xor(v, a))
                }
            }
            function tmul8(t, b) -> r {
                r := mload(add(t, shl(5, and(shr(120, b), 255))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(112, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(104, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(96, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(88, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(80, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(72, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(64, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(56, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(48, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(40, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(32, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(24, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(16, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(shr(8, b), 255)))))
                r := xor(shl(8, r), mload(add(t, shl(5, and(b, 255)))))
                let h := shr(128, r)
                r := xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
                h := shr(128, r)
                r := xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
            }
            function tbuild(t, a) {
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
            }
            function tmul(t, b) -> r {
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
                r := xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
                h := shr(128, r)
                r := xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
            }
            function gmul(a, b) -> r {
                let t := mload(0x40)
                tbuild(t, a)
                r := tmul(t, b)
            }
            function tab(ctx, i) -> t {
                t := add(mload(ctx), mul(i, 8192))
            }
            function alphaTab(ctx) -> t {
                t := tab(ctx, 65)
            }
            function skipTab(ctx, u) -> t {
                t := add(tab(ctx, 66), shl(9, u))
            }
            // The `eq` table of the ten coordinates at `point`, written from `at`.
            function eqInto(ctx, at, point) {
                mstore(at, 1)
                let t := tab(ctx, 64)
                for { let j := 0 } lt(j, 10) { j := add(j, 1) } {
                    tbuild8(t, mload(add(point, shl(5, j))))
                    let half := shl(j, 1)
                    for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                        let lo := mload(add(at, shl(5, i)))
                        let hi := tmul8(t, lo)
                        mstore(add(at, shl(5, add(i, half))), hi)
                        mstore(add(at, shl(5, i)), xor(lo, hi))
                    }
                }
            }
            // Writes entries `lo..hi` of the `eq` table of the ten coordinates at `point` from `at`,
            // through the tables of its low and high five coordinates, built at `half`.
            function eqFill(ctx, at, point, half, lo, hi) {
                let t := tab(ctx, 64)
                for { let part := 0 } lt(part, 2) { part := add(part, 1) } {
                    let e := add(half, shl(10, part))
                    mstore(e, 1)
                    for { let j := 0 } lt(j, 5) { j := add(j, 1) } {
                        tbuild8(t, mload(add(point, shl(5, add(j, mul(5, part))))))
                        let n := shl(j, 1)
                        for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                            let low := mload(add(e, shl(5, i)))
                            let high := tmul8(t, low)
                            mstore(add(e, shl(5, add(i, n))), high)
                            mstore(add(e, shl(5, i)), xor(low, high))
                        }
                    }
                }
                for { let i := lo } lt(i, hi) { i := add(i, 1) } {
                    mstore(add(at, shl(5, i)), gmul(mload(add(half, shl(5, and(i, 31)))), mload(add(add(half, 0x400), shl(5, shr(5, i))))))
                }
            }
            // `Σ_d kernel[lane][d]·pair[d]`, with the 8-bit multiplications written out.
            function laneDot(ctx, lane) -> acc {
                let base := add(mload(add(ctx, 0x20)), shl(11, lane))
                let t := tab(ctx, 0)
                for { let d := 0 } lt(d, 64) { d := add(d, 1) } {
                    let b := mload(add(base, shl(5, d)))
                    let r := mload(add(t, shl(5, and(shr(120, b), 255))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(112, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(104, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(96, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(88, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(80, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(72, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(64, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(56, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(48, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(40, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(32, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(24, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(16, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(shr(8, b), 255)))))
                    r := xor(shl(8, r), mload(add(t, shl(5, and(b, 255)))))
                    let h := shr(128, r)
                    r := xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
                    h := shr(128, r)
                    acc := xor(acc, xor(and(r, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h))))))
                    t := add(t, 8192)
                }
            }
            function roundValue(ctx, first) -> acc {
                let colp := mload(add(ctx, 0x80))
                for { let lane := 0 } lt(lane, 25) { lane := add(lane, 1) } {
                    acc := xor(acc, gmul(mload(add(colp, shl(5, add(first, lane)))), laneDot(ctx, lane)))
                }
            }
            function rcDot(ctx, r) -> acc {
                let bits := mload(add(mload(add(ctx, 0xe0)), mul(r, 8)))
                let skipp := mload(add(ctx, 0x100))
                let kp := mload(add(ctx, 0x20))
                for { let d := 0 } lt(d, 64) { d := add(d, 1) } {
                    let w := 0
                    for { let k := 0 } lt(k, 8) { k := add(k, 1) } {
                        let pos := byte(k, bits)
                        if lt(pos, 64) {
                            w := xor(w, mload(add(skipp, shl(5, and(sub(add(pos, 64), d), 63)))))
                        }
                    }
                    acc := xor(acc, gmul(mload(add(kp, shl(5, d))), w))
                }
            }
            function spread(ctx, from, amount) {
                let prep := add(mload(add(ctx, 0xa0)), mul(from, 22))
                let kp := mload(add(ctx, 0x20))
                for { let k := 0 } lt(k, 22) { k := add(k, 2) } {
                    let pair := shr(240, mload(add(prep, k)))
                    let slot := add(kp, shl(5, add(shl(6, shr(8, pair)), and(pair, 0xff))))
                    mstore(slot, xor(mload(slot), amount))
                }
            }
            function chiAdd(ctx, r) -> sum {
                let rowp := add(mload(add(ctx, 0x60)), shl(5, add(65, mul(25, r))))
                let at := alphaTab(ctx)
                for { let y := 0 } lt(y, 5) { y := add(y, 1) } {
                    for { let x := 0 } lt(x, 5) { x := add(x, 1) } {
                        let e := mload(add(rowp, shl(5, add(x, mul(5, y)))))
                        sum := xor(sum, e)
                        spread(ctx, add(mod(add(x, 1), 5), mul(5, y)), tmul(at, e))
                        spread(ctx, add(mod(add(x, 2), 5), mul(5, y)), e)
                    }
                }
            }
            function phiT(ctx) {
                let kp := mload(add(ctx, 0x20))
                let wp := mload(add(ctx, 0x40))
                let cp := add(wp, shl(5, 1600))
                let dp := add(cp, shl(5, 320))
                let rhop := mload(add(ctx, 0xc0))
                calldatacopy(cp, calldatasize(), shl(5, 320))
                for { let a := 0 } lt(a, 5) { a := add(a, 1) } {
                    let cs := add(cp, shl(11, a))
                    for { let b := 0 } lt(b, 5) { b := add(b, 1) } {
                        let rr := byte(0, mload(add(rhop, add(mul(5, a), b))))
                        let src := add(kp, shl(11, add(b, mul(5, mod(mul(2, sub(add(a, 5), b)), 5)))))
                        let dst := add(wp, shl(11, add(a, mul(5, b))))
                        let end := add(dst, 0x800)
                        let from := add(src, shl(5, rr))
                        let wrap := add(src, 0x800)
                        let cw := cs
                        for { } lt(dst, end) { dst := add(dst, 0x20) } {
                            if eq(from, wrap) { from := src }
                            let val := mload(from)
                            mstore(dst, val)
                            mstore(cw, xor(mload(cw), val))
                            from := add(from, 0x20)
                            cw := add(cw, 0x20)
                        }
                    }
                }
                for { let a := 0 } lt(a, 5) { a := add(a, 1) } {
                    let up := add(cp, shl(11, mod(add(a, 1), 5)))
                    let down := add(cp, shl(11, mod(add(a, 4), 5)))
                    let d := add(dp, shl(11, a))
                    for { let cc := 0 } lt(cc, 64) { cc := add(cc, 1) } {
                        mstore(add(d, shl(5, cc)), xor(mload(add(up, shl(5, cc))), mload(add(down, shl(5, and(add(cc, 1), 63))))))
                    }
                    for { let b := 0 } lt(b, 5) { b := add(b, 1) } {
                        let lane := shl(11, add(a, mul(5, b)))
                        let w := add(wp, lane)
                        let k := add(kp, lane)
                        let end := add(k, 0x800)
                        let dd := d
                        for { } lt(k, end) { k := add(k, 0x20) } {
                            mstore(k, xor(mload(w), mload(dd)))
                            w := add(w, 0x20)
                            dd := add(dd, 0x20)
                        }
                    }
                }
            }
            function buildTables(ctx, alpha) {
                let skipp := mload(add(ctx, 0x100))
                let zp := mload(add(ctx, 0x120))
                let pp := mload(add(ctx, 0x180))
                for { let u := 0 } lt(u, 64) { u := add(u, 1) } {
                    tbuild(skipTab(ctx, u), mload(add(skipp, shl(5, u))))
                }
                tbuild(alphaTab(ctx), alpha)
                for { let d := 0 } lt(d, 64) { d := add(d, 1) } {
                    let acc := 0
                    for { let u := 0 } lt(u, 64) { u := add(u, 1) } {
                        acc := xor(acc, tmul(skipTab(ctx, u), mload(add(zp, shl(5, and(add(u, d), 63))))))
                    }
                    mstore(add(pp, shl(5, d)), acc)
                    tbuild8(tab(ctx, d), acc)
                }
            }
            function loadPairs(ctx, alpha) {
                let pp := mload(add(ctx, 0x180))
                tbuild(alphaTab(ctx), alpha)
                for { let d := 0 } lt(d, 64) { d := add(d, 1) } {
                    tbuild8(tab(ctx, d), mload(add(pp, shl(5, d))))
                }
            }
            function start(ctx) -> psum {
                let kp := mload(add(ctx, 0x20))
                calldatacopy(kp, calldatasize(), shl(5, 1600))
                let rowp := mload(add(ctx, 0x60))
                for { let lane := 0 } lt(lane, 25) { lane := add(lane, 1) } {
                    let e := mload(add(rowp, shl(5, add(32, lane))))
                    psum := xor(psum, e)
                    mstore(add(kp, shl(11, lane)), tmul(alphaTab(ctx), e))
                }
            }
            function run(ctx, from, to) -> val, rcAcc, wsum {
                for { let i := from } lt(i, to) { i := add(i, 1) } {
                    let r := sub(23, i)
                    val := xor(val, roundValue(ctx, add(65, mul(25, r))))
                    rcAcc := xor(rcAcc, rcDot(ctx, r))
                    phiT(ctx)
                    wsum := xor(wsum, chiAdd(ctx, r))
                }
            }
            let cx := add(ctxArr, 0x20)
            switch mode
            case 0 {
                eqInto(cx, mload(add(cx, 0x60)), mload(add(cx, 0x140)))
                eqInto(cx, mload(add(cx, 0x80)), mload(add(cx, 0x160)))
                buildTables(cx, alphaIn)
                outPins := start(cx)
                outValue, outRc, outWeights := run(cx, 0, 24)
                outValue := xor(outValue, roundValue(cx, 0))
                outCol0 := mload(mload(add(cx, 0x80)))
            }
            case 1 {
                eqInto(cx, mload(add(cx, 0x60)), mload(add(cx, 0x140)))
                buildTables(cx, alphaIn)
                outPins := start(cx)
            }
            case 2 {
                let half := add(mload(add(cx, 0x40)), shl(5, 1920))
                let loR := add(65, mul(25, sub(24, toRound)))
                let hiR := add(65, mul(25, sub(24, fromRound)))
                eqFill(cx, mload(add(cx, 0x60)), mload(add(cx, 0x140)), half, loR, hiR)
                eqFill(cx, mload(add(cx, 0x80)), mload(add(cx, 0x160)), half, loR, hiR)
                loadPairs(cx, alphaIn)
                outValue, outRc, outWeights := run(cx, fromRound, toRound)
            }
            default {
                let half := add(mload(add(cx, 0x40)), shl(5, 1920))
                eqFill(cx, mload(add(cx, 0x80)), mload(add(cx, 0x160)), half, 0, 25)
                loadPairs(cx, alphaIn)
                outValue := roundValue(cx, 0)
                outCol0 := mload(mload(add(cx, 0x80)))
            }
        }
    }
}
