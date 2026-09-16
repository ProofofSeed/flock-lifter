// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "./Calldata.sol";
import {Constants} from "./Constants.sol";
import {GF2} from "./GF2.sol";
import {Transcript} from "./Transcript.sol";

/// An evaluation claim on the committed witness: a univariate-skip point, the remaining
/// coordinates in address order, and the value.
struct Claim {
    uint256 z;
    uint256[] x;
    uint256 value;
}

/// What the zerocheck hands on.
struct ZerocheckOut {
    uint256 z;
    uint256[] mlv;
    uint256[] rRest;
    uint256 a;
    uint256 b;
    uint256 c;
}

/// The equation the matrix discharge must close: `Σ_s comb[s]·zPartial[s] = running`, where
/// `comb` is the lincheck's folded row combination at `(alpha, beta)`, row point `(z, xInnerRest)`
/// and column point `rInnerRest`.
struct MatrixClaim {
    uint256 alpha;
    uint256 beta;
    uint256 z;
    uint256[] xInnerRest;
    uint256[] rInnerRest;
    uint256[] zPartial;
    uint256 running;
}

/// Flock's zerocheck and lincheck verifiers, and the lifter's published-word claim.
library Piop {
    uint256 internal constant K_LOG = 28;
    uint256 internal constant K_SKIP = 6;
    uint256 internal constant IO_BASE_BITS = 16 * 128;
    uint256 internal constant IO_WORDS = 16;

    error ZerocheckC();
    error ZerocheckFinal();
    error Degenerate();

    function bitsFor(uint256 n) internal pure returns (uint256 b) {
        while (n > 0) {
            ++b;
            n >>= 1;
        }
    }

    /// `(w, total)` with `w[i] = Π_{j≠i} (z + node_j)` and `total = Π_j (z + node_j)` over the 64
    /// φ₈ nodes starting at `base`.
    function leaveOneOut(bytes memory phi, uint256 base, uint256 z)
        internal
        pure
        returns (uint256[] memory w, uint256 total)
    {
        uint256[] memory diff = new uint256[](64);
        uint256[] memory pre = new uint256[](65);
        pre[0] = 1;
        for (uint256 i = 0; i < 64; ++i) {
            diff[i] = z ^ Constants.at(phi, base + i);
            pre[i + 1] = GF2.mul(pre[i], diff[i]);
        }
        total = pre[64];
        w = new uint256[](64);
        uint256 suf = 1;
        for (uint256 i = 64; i > 0; --i) {
            w[i - 1] = GF2.mul(pre[i - 1], suf);
            suf = GF2.mul(suf, diff[i - 1]);
        }
    }

    /// Flock's `lagrange_weights_naive(6, z)`: the Lagrange weights of the subspace
    /// `φ₈(0..64)` at `z`.
    function lagrange(bytes memory phi, uint256 z) internal pure returns (uint256[] memory w) {
        (w,) = leaveOneOut(phi, 0, z);
        for (uint256 i = 0; i < 64; ++i) {
            w[i] = GF2.mul(w[i], Constants.DEN6_INV);
        }
    }

    function fixedR(uint256 i) internal pure returns (uint256) {
        if (i == 0) return Constants.FIXED_R_0;
        if (i == 1) return Constants.FIXED_R_1;
        if (i == 2) return Constants.FIXED_R_2;
        if (i == 3) return Constants.FIXED_R_3;
        if (i == 4) return Constants.FIXED_R_4;
        if (i == 5) return Constants.FIXED_R_5;
        return Constants.FIXED_R_6;
    }

    /// Flock's zerocheck verifier over `2^m` bits, the running claim kept as a fraction so that
    /// no round divides.
    function zerocheck(uint256 tr, bytes memory phi, uint256 p, uint256 m)
        internal
        pure
        returns (uint256, ZerocheckOut memory out)
    {
        Transcript.label(tr, Constants.L_ZEROCHECK_0, Constants.L_ZEROCHECK_1, Constants.L_ZEROCHECK_LEN);
        Transcript.powSampleVec(tr, Calldata.nonce(p), bitsFor(m), K_SKIP);
        out.rRest = restPoint(tr, m);
        uint256 abAt = p + 8;
        Transcript.observeSliceFromCalldata(tr, abAt, 64);
        Transcript.observeSliceFromCalldata(tr, abAt + 64 * 16, 64);
        p = abAt + 128 * 16;
        out.z = Transcript.powSample(tr, Calldata.nonce(p), 7);
        (uint256 num, uint256 cEval) = roundOne(phi, abAt, out.z);
        if (cEval != Calldata.f128(p + 8)) revert ZerocheckC();
        out.c = cEval;
        uint256 den;
        (p, num, den) = rounds(tr, p + 24, out, num);
        out.a = Calldata.f128(p);
        out.b = Calldata.f128(p + 16);
        if (num != GF2.mul(GF2.mul(out.a, out.b), den)) revert ZerocheckFinal();
        Transcript.observe(tr, out.a);
        Transcript.observe(tr, out.b);
        return (p + 32, out);
    }

    function restPoint(uint256 tr, uint256 m) internal pure returns (uint256[] memory rest) {
        uint256 n = m - K_SKIP;
        uint256[] memory rOuter = Transcript.sampleVec(tr, n - 7);
        rest = new uint256[](n);
        for (uint256 i = 0; i < 7; ++i) {
            rest[i] = fixedR(i);
        }
        for (uint256 i = 7; i < n; ++i) {
            rest[i] = rOuter[i - 7];
        }
    }

    /// The combined round-one claim and the C evaluation, both interpolated at `z` from the
    /// round-one messages at `abAt`.
    function roundOne(bytes memory phi, uint256 abAt, uint256 z) internal pure returns (uint256 num, uint256 cEval) {
        (uint256[] memory loo,) = leaveOneOut(phi, 64, z);
        uint256 combined;
        for (uint256 i = 0; i < 64; ++i) {
            uint256 ci = Calldata.f128(abAt + 16 * (64 + i));
            cEval ^= GF2.mul(loo[i], ci);
            combined ^= GF2.mul(loo[i], ci ^ Calldata.f128(abAt + 16 * i));
        }
        cEval = GF2.mul(cEval, Constants.DEN6_INV);
        uint256 zS = 1;
        for (uint256 i = 0; i < 64; ++i) {
            zS = GF2.mul(zS, z ^ Constants.at(phi, i));
        }
        num = GF2.mul(GF2.mul(combined, zS), Constants.DEN7_INV) ^ cEval;
    }

    /// The multilinear rounds, over the fraction `num / den`.
    function rounds(uint256 tr, uint256 p, ZerocheckOut memory out, uint256 num)
        internal
        pure
        returns (uint256, uint256, uint256 den)
    {
        den = 1;
        uint256 n = out.rRest.length;
        out.mlv = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            uint256 e1 = Calldata.f128(p);
            uint256 einf = Calldata.f128(p + 16);
            Transcript.observe(tr, e1);
            Transcript.observe(tr, einf);
            uint256 rho = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            out.mlv[i] = rho;
            (num, den) = roundStep(num, den, out.rRest[i], e1, einf, rho);
        }
        return (p, num, den);
    }

    function roundStep(uint256 num, uint256 den, uint256 r, uint256 e1, uint256 einf, uint256 rho)
        internal
        pure
        returns (uint256, uint256)
    {
        uint256 denNext = GF2.mul(den, 1 ^ r);
        if (denNext == 0) revert Degenerate();
        uint256 tail = GF2.mul(e1, rho) ^ GF2.mul(einf, GF2.sq(rho) ^ rho);
        num = GF2.mul(num ^ GF2.mul(GF2.mul(r, e1), den), 1 ^ rho) ^ GF2.mul(denNext, tail);
        return (num, denNext);
    }

    /// Flock's lincheck verifier up to its last equation, which is returned for the matrix
    /// discharge, together with the witness claim it reduces to.
    function lincheck(uint256 tr, bytes memory phi, uint256 p, ZerocheckOut memory zc)
        internal
        pure
        returns (uint256, MatrixClaim memory mc, Claim memory ab)
    {
        uint256 inner = K_LOG - K_SKIP;
        Transcript.label(tr, Constants.L_LINCHECK_0, Constants.L_LINCHECK_1, Constants.L_LINCHECK_LEN);
        mc.alpha = Transcript.powSample(tr, Calldata.nonce(p), 1);
        mc.beta = Transcript.powSample(tr, Calldata.nonce(p + 8), 1);
        p += 16;
        uint256 running = GF2.mul(mc.alpha, zc.a) ^ zc.b ^ mc.beta;
        mc.rInnerRest = new uint256[](inner);
        for (uint256 i = 0; i < inner; ++i) {
            uint256 e1 = Calldata.f128(p);
            uint256 einf = Calldata.f128(p + 16);
            Transcript.observe(tr, e1);
            Transcript.observe(tr, einf);
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            running = GF2.mul(einf, GF2.sq(r)) ^ GF2.mul(running ^ einf, r) ^ running ^ e1;
            mc.rInnerRest[inner - 1 - i] = r;
        }
        mc.zPartial = new uint256[](64);
        for (uint256 i = 0; i < 64; ++i) {
            mc.zPartial[i] = Calldata.f128(p + 16 * i);
        }
        Transcript.observeSliceFromCalldata(tr, p, 64);
        p += 64 * 16;
        uint256 z2 = Transcript.powSample(tr, Calldata.nonce(p), K_SKIP);
        p += 8;
        mc.running = running;
        mc.z = zc.z;
        mc.xInnerRest = new uint256[](inner);
        for (uint256 i = 0; i < inner; ++i) {
            mc.xInnerRest[i] = zc.mlv[i];
        }
        ab.z = z2;
        ab.value = GF2.dot(lagrange(phi, z2), mc.zPartial);
        ab.x = new uint256[](zc.mlv.length);
        for (uint256 i = 0; i < inner; ++i) {
            ab.x[i] = mc.rInnerRest[i];
        }
        for (uint256 i = inner; i < zc.mlv.length; ++i) {
            ab.x[i] = zc.mlv[i];
        }
        return (p, mc, ab);
    }

    /// Observes the published words of every row, padded to `2^nu` rows by repeating the last.
    function observeWords(uint256 tr, uint256 wordsAt, uint256 live, uint256 nIo, uint256 nu) internal pure {
        Transcript.label(tr, Constants.L_WORDS_0, Constants.L_WORDS_1, Constants.L_WORDS_LEN);
        uint256 rows = 1 << nu;
        for (uint256 j = 0; j < rows; ++j) {
            uint256 row = j < live ? j : live - 1;
            for (uint256 w = 0; w < nIo; ++w) {
                Transcript.observe(tr, Calldata.native(wordsAt + 16 * (row * nIo + w)));
            }
        }
    }

    /// The published-word claim: its point from the transcript, its value from the words.
    function ioClaim(uint256 tr, bytes memory phi, uint256 wordsAt, uint256 live, uint256 nIo, uint256 nu)
        internal
        pure
        returns (Claim memory io)
    {
        io.z = Transcript.sample(tr);
        uint256 r6 = Transcript.sample(tr);
        uint256[] memory rWord = new uint256[](4);
        for (uint256 i = 0; i < 4; ++i) {
            rWord[i] = Transcript.sample(tr);
        }
        uint256[] memory xOuter = new uint256[](nu);
        for (uint256 i = 0; i < nu; ++i) {
            xOuter[i] = Transcript.sample(tr);
        }
        io.x = new uint256[](K_LOG - K_SKIP + nu);
        io.x[0] = r6;
        for (uint256 i = 0; i < 4; ++i) {
            io.x[1 + i] = rWord[i];
        }
        for (uint256 bit = 11; bit < K_LOG; ++bit) {
            io.x[bit - 6] = (IO_BASE_BITS >> bit) & 1;
        }
        for (uint256 i = 0; i < nu; ++i) {
            io.x[K_LOG - K_SKIP + i] = xOuter[i];
        }
        uint256[] memory table = linearTable(lagrange(phi, io.z), r6);
        io.value = ioValue(table, GF2.eqTable(rWord), GF2.eqTable(xOuter), wordsAt, live, nIo);
    }

    function ioValue(
        uint256[] memory table,
        uint256[] memory eWord,
        uint256[] memory eRow,
        uint256 wordsAt,
        uint256 live,
        uint256 nIo
    ) internal pure returns (uint256 value) {
        uint256 lastRow;
        for (uint256 j = 0; j < live; ++j) {
            uint256 acc = rowValue(table, eWord, wordsAt + 16 * j * nIo, nIo);
            if (j + 1 == live) {
                lastRow = acc;
            } else {
                value ^= GF2.mul(eRow[j], acc);
            }
        }
        uint256 tailWeight;
        for (uint256 j = live - 1; j < eRow.length; ++j) {
            tailWeight ^= eRow[j];
        }
        value ^= GF2.mul(tailWeight, lastRow);
    }

    function rowValue(uint256[] memory table, uint256[] memory eWord, uint256 rowAt, uint256 nIo)
        internal
        pure
        returns (uint256 acc)
    {
        for (uint256 w = 0; w < nIo; ++w) {
            acc ^= GF2.mul(eWord[w], applyTable(table, Calldata.native(rowAt + 16 * w)));
        }
    }

    /// The nibble tables of the linear map `word ↦ Σ_b bit_b(word)·weight_b`, where
    /// `weight_b = skip[b mod 64]·(b < 64 ? 1 + r6 : r6)`: entry `16·k + n` is the image of nibble
    /// `n` at nibble position `k`.
    function linearTable(uint256[] memory skip, uint256 r6) internal pure returns (uint256[] memory t) {
        uint256[] memory weight = new uint256[](128);
        for (uint256 b = 0; b < 64; ++b) {
            uint256 hi = GF2.mul(skip[b], r6);
            weight[b] = skip[b] ^ hi;
            weight[b + 64] = hi;
        }
        t = new uint256[](32 * 16);
        for (uint256 k = 0; k < 32; ++k) {
            uint256 base = 16 * k;
            for (uint256 n = 1; n < 16; ++n) {
                uint256 low = n & (~n + 1);
                uint256 bit = low == 1 ? 0 : low == 2 ? 1 : low == 4 ? 2 : 3;
                t[base + n] = t[base + (n ^ low)] ^ weight[4 * k + bit];
            }
        }
    }

    /// The linear map of `linearTable` applied to a word.
    function applyTable(uint256[] memory t, uint256 word) internal pure returns (uint256 acc) {
        assembly ("memory-safe") {
            let base := add(t, 0x20)
            for { let k := 0 } lt(k, 32) { k := add(k, 1) } {
                let n := and(shr(mul(k, 4), word), 15)
                acc := xor(acc, mload(add(base, shl(5, add(mul(k, 16), n)))))
            }
        }
    }
}
