// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Constants} from "../Constants.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
import {K} from "./K.sol";
import {W} from "./W.sol";
import {WrapKey} from "./WrapKey.sol";

/// The state of one verification of a wrapped lift.
struct Run {
    /// The outer transcript.
    uint256 tr;
    /// The calldata cursor.
    uint256 p;
    /// Where the public words sit in memory, sixteen bytes each.
    uint256 pub;
    /// Where the outer commitment's cap sits in calldata.
    uint256 capAt;
    /// The φ₈ nodes.
    bytes phi;
    /// The zerocheck's skip point, its `C` evaluation, its challenges and its equality point.
    uint256 zcZ;
    uint256 zcC;
    uint256[] mlv;
    uint256[] rRest;
    /// The lincheck's skip point, its witness claim, its column point, and where its collapsed
    /// witness and its table evaluations sit in calldata.
    uint256 lcZ;
    uint256 lcValue;
    uint256[] rr;
    uint256 zPartialAt;
    uint256 evalsAt;
    /// The Lagrange weights at the two skip points.
    uint256[] skipC;
    uint256[] skipAb;
    /// The wiring point, the three evaluations of the wiring's tables there, and where the
    /// gathered values sit in calldata.
    uint256[] rho;
    uint256 live;
    uint256 masked;
    uint256 sigma;
    uint256 gatherAt;
    /// The element class's zerocheck point, its lincheck's column point, and its two witness
    /// claims' values.
    uint256[] er;
    uint256[] ecol;
    uint256 ec;
    uint256 zEval;
}

/// The interactive proofs of a wrap's outer proof before its opening: Flock's zerocheck, union
/// lincheck, wiring argument and element class, with every evaluation of a committed table left
/// as a claim.
library WrapPiop {
    uint256 internal constant K_SKIP = 6;

    error ZerocheckC();
    error ZerocheckFinal();
    error Degenerate();
    error Lincheck();
    error WiringProducts();
    error WiringLayer();
    error WiringInputs();
    error WiringRecombination();
    error ElementZerocheck();
    error ElementTable();
    error ElementLincheck();

    uint256 internal constant L_ZEROCHECK_0 = 0x02000000000000000000000000000012666c6f636b2d7a65726f636865636b2d;
    uint256 internal constant L_ZEROCHECK_1 = 0x7630000000000000000000000000000000000000000000000000000000000000;
    uint256 internal constant L_LINCHECK_0 = 0x02000000000000000000000000000011666c6f636b2d6c696e636865636b2d76;
    uint256 internal constant L_LINCHECK_1 = 0x3000000000000000000000000000000000000000000000000000000000000000;
    // "flock-product-gkr-batched-v0"
    uint256 internal constant L_GKR_0 = 0x0200000000000000000000000000001c666c6f636b2d70726f647563742d676b;
    uint256 internal constant L_GKR_1 = 0x722d626174636865642d76300000000000000000000000000000000000000000;
    // "flock-element-union-zc-v0", "flock-element-union-lc-v0"
    uint256 internal constant L_EZC_0 = 0x02000000000000000000000000000019666c6f636b2d656c656d656e742d756e;
    uint256 internal constant L_EZC_1 = 0x696f6e2d7a632d76300000000000000000000000000000000000000000000000;
    uint256 internal constant L_ELC_1 = 0x696f6e2d6c632d76300000000000000000000000000000000000000000000000;

    function bitsFor(uint256 n) internal pure returns (uint256 b) {
        while (n > 0) {
            ++b;
            n >>= 1;
        }
    }

    /// Starts the outer transcript over the public segment, which it lays out in memory from the
    /// fixed words, the responses' published words at `wordsAt` and the words at the cursor; binds
    /// the statement; and forks the wiring argument's transcript, which it returns.
    function bind(Run memory x, uint256 wordsAt, bytes memory fixedWords) internal pure returns (uint256 child) {
        uint256 capLen = 32 << W.entry(WrapKey.OUTER_ROUNDS, 6, 1);
        uint256 tr;
        {
            uint256 capacity = 16 * WrapKey.NUM_PUBLIC + capLen + 4096;
            assembly ("memory-safe") {
                tr := mload(0x40)
                mstore(0x40, add(tr, capacity))
                mstore(tr, 0)
                mstore(add(tr, 0x20), 0)
            }
        }
        W.append(tr, WrapKey.BIND_PREFIX);
        uint256 img;
        assembly ("memory-safe") {
            img := add(add(tr, 0x40), mload(add(tr, 0x20)))
        }
        x.pub = img;
        W.append(tr, fixedWords);
        uint256 at = WrapKey.N_FIXED;
        uint256 p = x.p;
        bytes memory chunks = WrapKey.CHUNKS;
        uint256 n = chunks.length / 12;
        for (uint256 c = 0; c < n; ++c) {
            uint256 start = W.entry(chunks, 3 * c, 4);
            W.appendCalldata(tr, p, 16 * (start - at));
            p += 16 * (start - at);
            uint256 rows = W.entry(chunks, 3 * c + 1, 4);
            _rows(tr, wordsAt + 16 * WrapKey.N_IO * WrapKey.CHUNK * c, rows, W.entry(chunks, 3 * c + 2, 4));
            at = start + 16 * rows;
        }
        W.appendCalldata(tr, p, 16 * (WrapKey.NUM_PUBLIC - at));
        p += 16 * (WrapKey.NUM_PUBLIC - at);
        W.append(tr, WrapKey.BIND_MIXED);
        x.capAt = p;
        W.appendCalldata(tr, p, capLen);
        W.append(tr, WrapKey.BIND_CIRCUIT);
        W.appendCalldata(tr, p + capLen, 32);
        x.p = p + capLen + 32;
        child = W.fork(tr, "flock-par-wiring-v1", 1 << 14);
        // The public words stay where they are: the transcript continues in a fresh region.
        uint256 next;
        assembly ("memory-safe") {
            next := mload(0x40)
            mstore(0x40, add(next, 0x10080))
            mstore(next, mload(tr))
            mstore(add(next, 0x20), 0)
        }
        x.tr = next;
    }

    /// Appends a chunk's published words: `rows` rows of sixteen words, row `j` holding the
    /// `N_IO` words of response `min(j, live − 1)` at calldata `at`, each reversed from Flock's
    /// native layout, then zeros.
    function _rows(uint256 tr, uint256 at, uint256 rows, uint256 live) private pure {
        uint256 nIo = WrapKey.N_IO;
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let dst := add(add(tr, 0x40), l)
            for { let j := 0 } lt(j, rows) { j := add(j, 1) } {
                let r := j
                if iszero(lt(r, live)) { r := sub(live, 1) }
                let src := add(at, mul(r, shl(4, nIo)))
                for { let k := 0 } lt(k, 16) { k := add(k, 1) } {
                    let v := 0
                    if lt(k, nIo) {
                        v := shr(128, calldataload(add(src, shl(4, k))))
                        v := or(and(shr(8, v), 0x00ff00ff00ff00ff00ff00ff00ff00ff), shl(8, and(v, 0x00ff00ff00ff00ff00ff00ff00ff00ff)))
                        v := or(and(shr(16, v), 0x0000ffff0000ffff0000ffff0000ffff), shl(16, and(v, 0x0000ffff0000ffff0000ffff0000ffff)))
                        v := or(and(shr(32, v), 0x00000000ffffffff00000000ffffffff), shl(32, and(v, 0x00000000ffffffff00000000ffffffff)))
                        v := or(shr(64, v), shl(64, and(v, 0xffffffffffffffff)))
                    }
                    mstore(dst, shl(128, v))
                    dst := add(dst, 16)
                }
            }
            mstore(add(tr, 0x20), add(l, shl(8, rows)))
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

    /// One round of an equality-weighted quadratic sumcheck whose running claim is the fraction
    /// `num / den`, so that no round divides.
    function roundStep(uint256 num, uint256 den, uint256 r, uint256 e1, uint256 einf, uint256 rho)
        internal
        pure
        returns (uint256, uint256)
    {
        uint256 denNext = F.mul(den, 1 ^ r);
        if (denNext == 0) revert Degenerate();
        uint256 tail = F.mul(e1, rho) ^ F.mul(einf, F.sq(rho) ^ rho);
        num = F.mul(num ^ F.mul(F.mul(r, e1), den), 1 ^ rho) ^ F.mul(denNext, tail);
        return (num, denNext);
    }

    /// Flock's zerocheck over the Boolean region; returns its `A` and `B` evaluations.
    function zerocheck(Run memory x) internal pure returns (uint256 a, uint256 b) {
        uint256 tr = x.tr;
        uint256 p = x.p;
        uint256 m = WrapKey.M_BOOL;
        Transcript.label(tr, L_ZEROCHECK_0, L_ZEROCHECK_1, 48);
        Transcript.powSampleVec(tr, Calldata.nonce(p), bitsFor(m), K_SKIP);
        uint256 n = m - K_SKIP;
        {
            uint256[] memory rOuter = Transcript.sampleVec(tr, n - 7);
            x.rRest = new uint256[](n);
            for (uint256 i = 0; i < 7; ++i) {
                x.rRest[i] = fixedR(i);
            }
            for (uint256 i = 7; i < n; ++i) {
                x.rRest[i] = rOuter[i - 7];
            }
        }
        uint256 abAt = p + 8;
        Transcript.observeSliceFromCalldata(tr, abAt, 64);
        Transcript.observeSliceFromCalldata(tr, abAt + 64 * 16, 64);
        p = abAt + 128 * 16;
        x.zcZ = Transcript.powSample(tr, Calldata.nonce(p), 7);
        uint256 num;
        (num, x.zcC) = _roundOne(x.phi, abAt, x.zcZ);
        if (x.zcC != Calldata.f128(p + 8)) revert ZerocheckC();
        p += 24;
        uint256 den = 1;
        x.mlv = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            uint256 e1 = Calldata.f128(p);
            uint256 einf = Calldata.f128(p + 16);
            Transcript.observe(tr, e1);
            Transcript.observe(tr, einf);
            uint256 rho = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            x.mlv[i] = rho;
            (num, den) = roundStep(num, den, x.rRest[i], e1, einf, rho);
        }
        a = Calldata.f128(p);
        b = Calldata.f128(p + 16);
        if (num != F.mul(F.mul(a, b), den)) revert ZerocheckFinal();
        Transcript.observe(tr, a);
        Transcript.observe(tr, b);
        x.p = p + 32;
    }

    /// The combined round-one claim and the `C` evaluation, both interpolated at `z` from the
    /// round-one messages at `abAt`.
    function _roundOne(bytes memory phi, uint256 abAt, uint256 z) private pure returns (uint256 num, uint256 cEval) {
        (uint256[] memory loo,) = W.leaveOneOut(phi, 64, z);
        cEval = K.dotCalldata(W.ptr(loo), abAt + 16 * 64, 64);
        uint256 combined = cEval ^ K.dotCalldata(W.ptr(loo), abAt, 64);
        cEval = F.mul(cEval, Constants.DEN6_INV);
        uint256 zS = 1;
        for (uint256 i = 0; i < 64; ++i) {
            zS = F.mul(zS, z ^ Constants.at(phi, i));
        }
        num = F.mul(F.mul(combined, zS), Constants.DEN7_INV) ^ cEval;
    }

    /// Flock's lincheck over the union's columns, its reported table evaluations checked against
    /// its last equation.
    function lincheck(Run memory x, uint256 a, uint256 b) internal pure {
        uint256 tr = x.tr;
        uint256 p = x.p;
        uint256 rounds = WrapKey.M_BOOL - WrapKey.NU - K_SKIP;
        Transcript.label(tr, L_LINCHECK_0, L_LINCHECK_1, 48);
        uint256 alpha = Transcript.powSample(tr, Calldata.nonce(p), 1);
        p += 8;
        uint256 target = F.mul(alpha, a) ^ b;
        bytes memory bools = WrapKey.BOOLS;
        uint256[] memory betas = new uint256[](WrapKey.N_BOOL);
        for (uint256 t = 0; t < WrapKey.N_BOOL; ++t) {
            if (W.read(bools, 12 * t + 3, 1) == 1) {
                betas[t] = Transcript.powSample(tr, Calldata.nonce(p), 1);
                p += 8;
                target ^= F.mul(betas[t], W.prefixSum(x.mlv, 1, WrapKey.NU, W.read(bools, 12 * t + 8, 4)));
            }
        }
        x.rr = new uint256[](rounds);
        for (uint256 i = 0; i < rounds; ++i) {
            uint256 e1 = Calldata.f128(p);
            uint256 einf = Calldata.f128(p + 16);
            Transcript.observe(tr, e1);
            Transcript.observe(tr, einf);
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            target = W.quadratic(target, e1, einf, r);
            x.rr[rounds - 1 - i] = r;
        }
        x.zPartialAt = p;
        Transcript.observeSliceFromCalldata(tr, p, 64);
        p += 64 * 16;
        x.lcZ = Transcript.powSample(tr, Calldata.nonce(p), K_SKIP);
        p += 8;
        x.skipAb = W.lagrange(x.phi, x.lcZ);
        x.lcValue = K.dotCalldata(W.ptr(x.skipAb), x.zPartialAt, 64);
        x.evalsAt = p;
        x.p = p + 32 * WrapKey.N_BOOL;
        if (_reported(x, bools, betas, alpha, rounds) != target) revert Lincheck();
    }

    /// The lincheck's last equation's right-hand side from the reported table evaluations.
    function _reported(Run memory x, bytes memory bools, uint256[] memory betas, uint256 alpha, uint256 rounds)
        private
        pure
        returns (uint256 acc)
    {
        for (uint256 t = 0; t < WrapKey.N_BOOL; ++t) {
            uint256 inner = W.read(bools, 12 * t, 1) - K_SKIP;
            uint256 prefix = W.read(bools, 12 * t + 1, 1);
            uint256 pw = W.eqWeight(x.rr, inner, rounds - inner, prefix);
            uint256 term = F.mul(
                W.eqWeight(x.mlv, WrapKey.NU + inner, rounds - inner, prefix),
                F.mul(alpha, Calldata.f128(x.evalsAt + 32 * t)) ^ Calldata.f128(x.evalsAt + 32 * t + 16)
            );
            if (W.read(bools, 12 * t + 3, 1) == 1) {
                uint256 col = W.read(bools, 12 * t + 4, 4);
                term ^= F.mul(
                    betas[t],
                    F.mul(W.eqWeight(x.rr, 0, inner, col >> K_SKIP), Calldata.f128(x.zPartialAt + 16 * (col & 63)))
                );
            }
            acc ^= F.mul(pw, term);
        }
    }

    /// The wiring argument on its transcript `ch`: the grand-product layers, the input check
    /// against the supplied evaluations of the live mask and of the masked identity, and the
    /// recombination of the gathered values with the public words.
    function wiring(Run memory x, uint256 ch) internal pure {
        uint256 p = x.p;
        Transcript.label(ch, L_GKR_0, L_GKR_1, 48);
        uint256 alpha = Transcript.powSample(ch, Calldata.nonce(p), WrapKey.GKR_BITS);
        uint256 beta = Transcript.sample(ch);
        uint256[2] memory claim = [Calldata.f128(p + 8), Calldata.f128(p + 24)];
        p += 40;
        Transcript.observe(ch, claim[0]);
        Transcript.observe(ch, claim[1]);
        if (claim[0] != claim[1]) revert WiringProducts();
        x.rho = new uint256[](WrapKey.MU);
        uint256[] memory next = new uint256[](WrapKey.MU);
        for (uint256 k = 0; k < WrapKey.MU; ++k) {
            p = _layer(ch, p, k, claim, x.rho, next);
            (x.rho, next) = (next, x.rho);
        }
        uint256 f = Calldata.f128(p);
        {
            uint256 g = Calldata.f128(p + 16);
            x.sigma = Calldata.f128(p + 32);
            x.live = Calldata.f128(p + 48);
            x.masked = Calldata.f128(p + 64);
            uint256 tail = F.mul(beta ^ 1, x.live) ^ 1;
            if (claim[0] != f ^ F.mul(alpha, x.masked) ^ tail || claim[1] != g ^ F.mul(alpha, x.sigma) ^ tail || f != g) {
                revert WiringInputs();
            }
            Transcript.observe(ch, f);
            Transcript.observe(ch, g);
            Transcript.observe(ch, x.sigma);
        }
        p += 80;
        x.gatherAt = p;
        x.p = p + 16 * WrapKey.N_GATE;
        uint256[] memory eqSlot = W.eqTable(x.rho, WrapKey.NU, WrapKey.MU - WrapKey.NU, 1);
        uint256 acc = F.mul(eqSlot[WrapKey.N_GATE], publicEval(x.pub, WrapKey.NUM_PUBLIC, x.rho, WrapKey.NU))
            ^ K.dotCalldata(W.ptr(eqSlot), p, WrapKey.N_GATE);
        if (acc != f) revert WiringRecombination();
    }

    /// One layer of the grand products: its rounds over the previous layer's `point`, its gate
    /// check, and the next claims and point.
    function _layer(uint256 ch, uint256 p, uint256 k, uint256[2] memory claim, uint256[] memory point, uint256[] memory next)
        private
        pure
        returns (uint256)
    {
        uint256 lambda = Transcript.powSample(ch, Calldata.nonce(p), 1);
        p += 8;
        uint256 num = claim[0] ^ F.mul(lambda, claim[1]);
        uint256 den = 1;
        for (uint256 i = 0; i < k; ++i) {
            uint256 g1 = Calldata.f128(p);
            uint256 ginf = Calldata.f128(p + 16);
            Transcript.observe(ch, g1);
            Transcript.observe(ch, ginf);
            uint256 rho = Transcript.powSample(ch, Calldata.nonce(p + 32), 2);
            p += 40;
            next[i] = rho;
            (num, den) = roundStep(num, den, point[i], g1, ginf, rho);
        }
        uint256 v0 = Calldata.f128(p);
        uint256 v1 = Calldata.f128(p + 16);
        uint256 v2 = Calldata.f128(p + 32);
        uint256 v3 = Calldata.f128(p + 48);
        Transcript.observe(ch, v0);
        Transcript.observe(ch, v1);
        Transcript.observe(ch, v2);
        Transcript.observe(ch, v3);
        if (num != F.mul(F.mul(v0, v1) ^ F.mul(lambda, F.mul(v2, v3)), den)) revert WiringLayer();
        uint256 c = Transcript.powSample(ch, Calldata.nonce(p + 64), 1);
        claim[0] = v0 ^ F.mul(c, v0 ^ v1);
        claim[1] = v2 ^ F.mul(c, v2 ^ v3);
        next[k] = c;
        return p + 72;
    }

    /// The multilinear extension of the `n` sixteen-byte words at memory `img`, zero-padded, at
    /// the first `vars` coordinates of `point`.
    function publicEval(uint256 img, uint256 n, uint256[] memory point, uint256 vars) internal pure returns (uint256 acc) {
        // Blocks of 64 words against the six low coordinates, then the blocks against the rest:
        // the coordinates beyond the blocks' index weigh their zero side.
        uint256 blocks = (n + 63) / 64;
        uint256 high;
        while ((1 << high) < blocks) {
            ++high;
        }
        uint256 seed = 1;
        for (uint256 i = 6 + high; i < vars; ++i) {
            seed = F.mul(seed, 1 ^ point[i]);
        }
        uint256[] memory low = W.eqTable(point, 0, 6, 1);
        uint256[] memory top = W.eqTable(point, 6, high, seed);
        uint256[] memory inner = new uint256[](blocks);
        // A block equal to the one before it, as the rows that pad a chunk are, has its value.
        bytes32 previous;
        for (uint256 b = 0; b < blocks; ++b) {
            uint256 len = n - 64 * b < 64 ? n - 64 * b : 64;
            uint256 at = img + 16 * 64 * b;
            bytes32 h;
            assembly ("memory-safe") {
                h := keccak256(at, shl(4, len))
            }
            inner[b] = b > 0 && h == previous ? inner[b - 1] : K.dotPacked(W.ptr(low), at, len);
            previous = h;
        }
        return K.dot(W.ptr(top), W.ptr(inner), blocks);
    }

    /// `Σ_i eq[i]·v[i]` for the sparse vector at byte `at` of `data`.
    function _sparseDot(bytes memory data, uint256 at, uint256[] memory eq) private pure returns (uint256 acc) {
        uint256 n = W.read(data, at, 2);
        at += 2;
        for (uint256 i = 0; i < n; ++i) {
            acc ^= F.mul(eq[W.read(data, at, 1)], W.read(data, at + 1, 16));
            at += 17;
        }
    }

    /// `Σ_{r,c} row[r]·col[c]·m[r][c]` for the sparse matrix at byte `at` of `data`.
    function _bilinear(bytes memory data, uint256 at, uint256[] memory row, uint256[] memory col) private pure returns (uint256 acc) {
        uint256 rows = W.read(data, at, 2);
        at += 2;
        for (uint256 i = 0; i < rows; ++i) {
            uint256 r = W.read(data, at, 1);
            uint256 n = W.read(data, at + 1, 1);
            at += 2;
            uint256 inner;
            for (uint256 e = 0; e < n; ++e) {
                uint256 c = col[W.read(data, at, 1)];
                if (W.read(data, at + 1, 1) == 0) {
                    inner ^= c;
                    at += 2;
                } else {
                    inner ^= F.mul(W.read(data, at + 2, 16), c);
                    at += 18;
                }
            }
            acc ^= F.mul(row[r], inner);
        }
    }

    /// The element class's zerocheck and lincheck, its tables evaluated in place.
    function element(Run memory x, bytes memory elems, bytes memory data) internal pure {
        uint256 tr = x.tr;
        uint256 p = x.p;
        uint256 vars = WrapKey.M_ELEM - 7;
        Transcript.label(tr, L_EZC_0, L_EZC_1, 48);
        {
            uint256[] memory tau = Transcript.powSampleVec(tr, Calldata.nonce(p), bitsFor(vars), vars);
            p += 8;
            uint256 num;
            uint256 den = 1;
            x.er = new uint256[](vars);
            for (uint256 i = 0; i < vars; ++i) {
                uint256 g1 = Calldata.f128(p);
                uint256 ginf = Calldata.f128(p + 16);
                Transcript.observe(tr, g1);
                Transcript.observe(tr, ginf);
                uint256 rho = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
                p += 40;
                x.er[i] = rho;
                (num, den) = roundStep(num, den, tau[i], g1, ginf, rho);
            }
            x.ec = Calldata.f128(p + 32);
            if (num != F.mul(F.mul(Calldata.f128(p), Calldata.f128(p + 16)) ^ x.ec, den)) revert ElementZerocheck();
        }
        uint256 va = Calldata.f128(p);
        uint256 vb = Calldata.f128(p + 16);
        Transcript.observe(tr, va);
        Transcript.observe(tr, vb);
        Transcript.observe(tr, x.ec);
        p += 48;
        uint256[][] memory rows = new uint256[][](WrapKey.N_ELEM);
        uint256 cols = vars - WrapKey.NU;
        for (uint256 t = 0; t < WrapKey.N_ELEM; ++t) {
            uint256 kappa = W.read(elems, 18 * t, 1);
            rows[t] = W.eqTable(x.er, WrapKey.NU, kappa, 1);
            uint256 w = W.eqWeight(x.er, WrapKey.NU + kappa, cols - kappa, W.read(elems, 18 * t + 1, 1));
            va ^= F.mul(w, _sparseDot(data, W.read(elems, 18 * t + 10, 4), rows[t]));
            vb ^= F.mul(w, _sparseDot(data, W.read(elems, 18 * t + 14, 4), rows[t]));
        }
        Transcript.label(tr, L_EZC_0, L_ELC_1, 48);
        uint256 alpha = Transcript.powSample(tr, Calldata.nonce(p), 1);
        p += 8;
        uint256 running = va ^ F.mul(alpha, vb);
        x.ecol = new uint256[](cols);
        for (uint256 i = 0; i < cols; ++i) {
            uint256 e1 = Calldata.f128(p);
            uint256 einf = Calldata.f128(p + 16);
            Transcript.observe(tr, e1);
            Transcript.observe(tr, einf);
            uint256 rho = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            running = W.quadratic(running, e1, einf, rho);
            x.ecol[cols - 1 - i] = rho;
        }
        x.zEval = Calldata.f128(p);
        p += 16;
        x.p = p + 32 * WrapKey.N_ELEM;
        if (F.mul(_elementTables(x, elems, data, rows, p, alpha), x.zEval) != running) revert ElementLincheck();
    }

    /// Checks the element tables' reported evaluations at calldata `p` against the tables, and
    /// returns their combination in the lincheck's last equation.
    function _elementTables(Run memory x, bytes memory elems, bytes memory data, uint256[][] memory rows, uint256 p, uint256 alpha)
        private
        pure
        returns (uint256 acc)
    {
        uint256 cols = x.ecol.length;
        for (uint256 t = 0; t < WrapKey.N_ELEM; ++t) {
            uint256 kappa = W.read(elems, 18 * t, 1);
            uint256 prefix = W.read(elems, 18 * t + 1, 1);
            uint256 ta = Calldata.f128(p + 32 * t);
            uint256 tb = Calldata.f128(p + 32 * t + 16);
            uint256[] memory eqCol = W.eqTable(x.ecol, 0, kappa, 1);
            if (
                _bilinear(data, W.read(elems, 18 * t + 2, 4), rows[t], eqCol) != ta
                    || _bilinear(data, W.read(elems, 18 * t + 6, 4), rows[t], eqCol) != tb
            ) revert ElementTable();
            uint256 w = F.mul(
                W.eqWeight(x.er, WrapKey.NU + kappa, cols - kappa, prefix), W.eqWeight(x.ecol, kappa, cols - kappa, prefix)
            );
            acc ^= F.mul(w, ta ^ F.mul(alpha, tb));
        }
    }
}
