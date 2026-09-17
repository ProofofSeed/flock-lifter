// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "./Calldata.sol";
import {Constants, LigeritoConfig} from "./Constants.sol";
import {GF2} from "./GF2.sol";
import {Claim, Piop} from "./Piop.sol";
import {Meter} from "./Meter.sol";
import {Residual} from "./Residual.sol";
import {Transcript} from "./Transcript.sol";

/// An out-of-domain sample of the Ligerito verifier.
struct Ood {
    uint256[] point;
    uint256 beta;
    uint256 split;
}

/// The queried-consistency equation of one Ligerito level.
struct Consistency {
    uint256 logCols;
    uint256[] queries;
    uint256[] alpha;
    uint256 beta;
    uint256 start;
}

/// The ring-switched claims, as the residual evaluation needs them.
struct Switched {
    Claim[] claims;
    uint256[][] eqs;
    uint256[] gammas;
}

/// The running state of the Ligerito verifier.
struct LigeritoState {
    uint256 tr;
    uint256 p;
    uint256 claim;
    uint256 c;
    uint256 b;
    uint256 a;
    uint256 logN;
    uint256 splitDim;
    uint256 capAt;
    uint256 capLen;
    uint256 prevLanes;
    uint256 prevCols;
    uint256 prevRate;
    uint256 nOod;
    uint256 nCons;
    uint256 end;
    uint256 target;
    uint256 openAt;
    uint256 openLen;
    Ood[] oods;
    Consistency[] cons;
    uint256[] initial;
    uint256[][] levels;
}

/// Flock's batched opening of evaluation claims on a Ligerito commitment: the ring switch of
/// every claim, then the Ligerito verifier over GF(2^256) with its stratified queries and
/// SHA-256 Merkle openings.
library Opening {
    error RingSwitchClaim();
    error MerklePath();
    error ResidualMismatch();
    error Trailing();

    function sha256At(uint256 ptr, uint256 len) internal view returns (bytes32 h) {
        assembly ("memory-safe") {
            if iszero(staticcall(gas(), 2, ptr, len, 0, 32)) { revert(0, 0) }
            h := mload(0)
        }
    }

    function sha256Pair(bytes32 l, bytes32 r) internal view returns (bytes32 h) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, l)
            mstore(add(ptr, 0x20), r)
            if iszero(staticcall(gas(), 2, ptr, 64, 0, 32)) { revert(0, 0) }
            h := mload(0)
        }
    }

    /// The batched opening of `claims` against the commitment whose cap sits at `capAt`.
    function verify(
        uint256 tr,
        bytes memory phi,
        uint256 p,
        uint256 end,
        LigeritoConfig memory cfg,
        uint256 m,
        uint256 capAt,
        uint256 capLen,
        Claim[] memory claims
    ) internal {
        Transcript.label(tr, Constants.L_OPEN_0, Constants.L_OPEN_1, Constants.L_OPEN_LEN);
        uint256 n = claims.length;
        Switched memory sw;
        sw.claims = claims;
        sw.eqs = new uint256[][](n);
        uint256[] memory sums = new uint256[](n);
        for (uint256 c = 0; c < n; ++c) {
            (sw.eqs[c], sums[c]) = ringSwitch(tr, phi, p, claims[c]);
            p += 128 * 16 + 8;
        }
        Meter.mark(10);
        if (n == 1) {
            sw.gammas = Transcript.sampleVec(tr, 1);
        } else {
            sw.gammas = Transcript.powSampleVec(tr, Calldata.nonce(p), 6, n);
            p += 8;
        }
        uint256 target;
        for (uint256 c = 0; c < n; ++c) {
            target ^= GF2.mul(sw.gammas[c], sums[c]);
        }
        LigeritoState memory st;
        st.tr = tr;
        st.p = p;
        st.end = end;
        st.logN = m - 7;
        st.target = target;
        st.capAt = capAt;
        st.capLen = capLen;
        ligerito(st, cfg, sw);
    }

    /// One claim's ring switch: checks the claim against the sliced message at `p` and returns
    /// the `eq` table of the sampled point with the switched sumcheck claim.
    function ringSwitch(uint256 tr, bytes memory phi, uint256 p, Claim memory claim)
        internal
        pure
        returns (uint256[] memory eq, uint256 sum)
    {
        Transcript.label(tr, Constants.L_RING_0, Constants.L_RING_1, Constants.L_RING_LEN);
        Transcript.observeSliceFromCalldata(tr, p, 128);
        if (claimCheck(Piop.lagrange(phi, claim.z), claim.x[0], p) != claim.value) revert RingSwitchClaim();
        uint256[] memory rdp = Transcript.powSampleVec(tr, Calldata.nonce(p + 128 * 16), 3, 7);
        eq = GF2.eqTable(rdp);
        uint256[] memory table = Piop.bitTable(eq);
        for (uint256 i = 128; i > 0; --i) {
            uint256 l = Piop.applyTable(table, Calldata.f128(p + 16 * (i - 1)));
            uint256 top = sum >> 127;
            sum = ((sum << 1) & GF2.M128) ^ (top * 0x87) ^ l;
        }
    }

    function claimCheck(uint256[] memory skip, uint256 x0, uint256 p) internal pure returns (uint256 acc) {
        for (uint256 i = 0; i < 64; ++i) {
            uint256 lo = Calldata.f128(p + 16 * i);
            uint256 hi = Calldata.f128(p + 16 * (64 + i));
            acc ^= GF2.mul(skip[i], lo ^ GF2.mul(x0, lo ^ hi));
        }
    }

    function message(LigeritoState memory st) internal pure returns (uint256 u0, uint256 u2) {
        u0 = Calldata.f256(st.p);
        u2 = Calldata.f256(st.p + 32);
        Transcript.observeF256FromCalldata(st.tr, st.p);
        Transcript.observeF256FromCalldata(st.tr, st.p + 32);
        st.p += 64;
    }

    function fromMsg(LigeritoState memory st, uint256 u0, uint256 u2, uint256 claim) internal pure {
        st.c = u0;
        st.b = claim ^ u2;
        st.a = u2;
    }

    function evalQuad(LigeritoState memory st, uint256 r) internal pure returns (uint256) {
        return st.c ^ GF2.mul256(r, st.b) ^ GF2.mul256(GF2.mul256(r, r), st.a);
    }

    function foldQuad(LigeritoState memory st, uint256 u0, uint256 u2, uint256 claim, uint256 alpha) internal pure {
        st.c ^= GF2.mul256By128(u0, alpha);
        st.b ^= GF2.mul256By128(claim ^ u2, alpha);
        st.a ^= GF2.mul256By128(u2, alpha);
    }

    function sampleF256(uint256 tr) internal pure returns (uint256) {
        uint256[] memory w = Transcript.sampleVec(tr, 2);
        return (w[1] << 128) | w[0];
    }

    function ceilLog2(uint256 n) internal pure returns (uint256 r) {
        if (n <= 1) return 0;
        n -= 1;
        while (n > 0) {
            ++r;
            n >>= 1;
        }
    }

    function readCap(LigeritoState memory st, uint256 depth) internal pure {
        st.capAt = st.p;
        st.capLen = 1 << depth;
        Transcript.header(st.tr, 5, 0, 32 << depth);
        Transcript.bytesFromCalldata(st.tr, st.p, 32 << depth);
        st.p += 32 << depth;
    }

    function ood(LigeritoState memory st, LigeritoConfig memory cfg, uint256 level, uint256 dim, uint256 split, bool intro)
        internal
        pure
    {
        for (uint256 j = 0; j < cfg.oodSamples[level]; ++j) {
            uint256[] memory point = Transcript.sampleVec(st.tr, dim);
            uint256 y = Calldata.f128(st.p);
            st.p += 16;
            Transcript.observe(st.tr, y);
            uint256 u0;
            uint256 u2;
            if (intro) {
                (u0, u2) = message(st);
            }
            uint256 bits = cfg.claimBits[intro ? level : 0];
            uint256 beta = Transcript.powSample(st.tr, Calldata.nonce(st.p), bits);
            st.p += 8;
            if (intro) {
                foldQuad(st, u0, u2, y, beta);
            }
            st.claim ^= GF2.mul(beta, y);
            st.oods[st.nOod++] = Ood(point, beta, split);
        }
    }

    function queries(LigeritoState memory st, LigeritoConfig memory cfg, uint256 level, uint256 blockLen)
        internal
        pure
        returns (uint256[] memory qs, uint256[] memory alpha)
    {
        uint256 count = cfg.queries[level];
        uint256[] memory words = Transcript.powSampleVec(st.tr, Calldata.nonce(st.p), cfg.grindingBits[level], count);
        alpha = Transcript.powSampleVec(st.tr, Calldata.nonce(st.p + 8), cfg.consistencyBits[level], ceilLog2(count));
        st.p += 16;
        uint256 d = cfg.logBlockLens[level];
        require(blockLen == 1 << d, "level shape");
        qs = new uint256[](count);
        uint256 at;
        uint256[] memory depths = cfg.depths[level];
        for (uint256 i = 0; i < depths.length; ++i) {
            uint256 c = depths[i];
            uint256 lo = d - c;
            for (uint256 s = 0; s < (1 << c); ++s) {
                qs[at] = (s << lo) | (words[at] & ((1 << lo) - 1));
                ++at;
            }
        }
    }

    /// Checks a level's opened rows against the cap at `st.openAt` and returns their batched sum.
    function opens(
        LigeritoState memory st,
        LigeritoConfig memory cfg,
        uint256 level,
        uint256[] memory qs,
        uint256 width,
        uint256[] memory lanes,
        uint256[] memory alpha
    ) internal view returns (uint256 enforced) {
        uint256 c1 = cfg.depths[level][0];
        require(st.openLen == 1 << c1, "cap shape");
        uint256 rowsAt = st.p;
        uint256 pathLen = cfg.logBlockLens[level] - c1;
        uint256 pathsAt = rowsAt + qs.length * width * 16;
        for (uint256 r = 0; r < qs.length; ++r) {
            uint256 root = pathRoot(rowsAt + r * width * 16, width, pathsAt + r * pathLen * 32, pathLen, qs[r]);
            if (root != Calldata.f256(st.openAt + 32 * (qs[r] >> pathLen))) revert MerklePath();
        }
        st.p = pathsAt + qs.length * pathLen * 32;
        enforced = enforcedSum(rowsAt, qs.length, width, lanes, alpha);
    }

    /// The cap node above a row, hashed from the row and its path.
    function pathRoot(uint256 rowAt, uint256 width, uint256 pathAt, uint256 pathLen, uint256 idx)
        internal
        view
        returns (uint256)
    {
        uint256 buf;
        assembly ("memory-safe") {
            buf := mload(0x40)
            calldatacopy(buf, rowAt, mul(width, 16))
        }
        bytes32 acc = sha256At(buf, width * 16);
        for (uint256 k = 0; k < pathLen; ++k) {
            bytes32 sib = bytes32(Calldata.f256(pathAt + 32 * k));
            acc = idx & 1 == 0 ? sha256Pair(acc, sib) : sha256Pair(sib, acc);
            idx >>= 1;
        }
        return uint256(acc);
    }

    /// `Σ_l lw[l] · Σ_r rw[r]·row[r][l]` with `lw`, `rw` the `eq` tables of `lanes` and `alpha`.
    function enforcedSum(uint256 rowsAt, uint256 nq, uint256 width, uint256[] memory lanes, uint256[] memory alpha)
        internal
        pure
        returns (uint256 enforced)
    {
        uint256[] memory lw = GF2.eqTable256(lanes);
        uint256[] memory rw = GF2.eqTable(alpha);
        for (uint256 l = 0; l < width; ++l) {
            uint256 col;
            for (uint256 r = 0; r < nq; ++r) {
                col ^= GF2.mul(rw[r], Calldata.native(rowsAt + 16 * (r * width + l)));
            }
            enforced ^= GF2.mul256By128(lw[l], col);
        }
    }

    /// `k` sumcheck rounds over GF(2^256), returning their challenges.
    function sumcheck(LigeritoState memory st, uint256 k) internal pure returns (uint256[] memory chs) {
        chs = new uint256[](k);
        for (uint256 j = 0; j < k; ++j) {
            uint256 ch = sampleF256(st.tr);
            st.claim = evalQuad(st, ch);
            chs[j] = ch;
            (uint256 u0, uint256 u2) = message(st);
            fromMsg(st, u0, u2, st.claim);
        }
    }

    /// A level's query phase and opening, returning the queries, the consistency point and the
    /// batched sum of the opened rows.
    function levelOpen(
        LigeritoState memory st,
        LigeritoConfig memory cfg,
        uint256 level,
        uint256 blockLen,
        uint256 width,
        uint256[] memory lanes
    ) internal view returns (Consistency memory cn, uint256 enforced) {
        (cn.queries, cn.alpha) = queries(st, cfg, level, blockLen);
        enforced = opens(st, cfg, level, cn.queries, width, lanes, cn.alpha);
    }

    /// Introduces a level's consistency claim into the running sumcheck and records it.
    function introduce(
        LigeritoState memory st,
        Consistency memory cn,
        uint256 enforced,
        uint256 bits,
        uint256 logCols,
        uint256 start
    ) internal pure {
        (uint256 u0, uint256 u2) = message(st);
        uint256 beta = Transcript.powSample(st.tr, Calldata.nonce(st.p), bits);
        st.p += 8;
        foldQuad(st, u0, u2, enforced, beta);
        st.claim ^= GF2.mul256By128(enforced, beta);
        cn.beta = beta;
        cn.logCols = logCols;
        cn.start = start;
        st.cons[st.nCons++] = cn;
    }

    function ligerito(LigeritoState memory st, LigeritoConfig memory cfg, Switched memory sw) internal {
        st.oods = new Ood[](32);
        st.cons = new Consistency[](cfg.steps + 1);
        st.levels = new uint256[][](cfg.steps);
        Transcript.label(st.tr, Constants.L_LIGERITO_0, Constants.L_LIGERITO_1, Constants.L_LIGERITO_LEN);
        Transcript.observe(st.tr, st.target);
        Transcript.header(st.tr, 5, 0, st.capLen * 32);
        Transcript.bytesFromCalldata(st.tr, st.capAt, st.capLen * 32);
        st.claim = st.target;
        ood(st, cfg, 0, st.logN, type(uint256).max, false);
        (uint256 u0, uint256 u2) = message(st);
        fromMsg(st, u0, u2, st.claim);
        st.initial = sumcheck(st, cfg.initialK);
        uint256 cap0At = st.capAt;
        uint256 cap0Len = st.capLen;
        st.splitDim = st.logN - cfg.initialK + 1;
        readCap(st, cfg.depths[1][0]);
        ood(st, cfg, 1, st.splitDim, 0, true);
        {
            uint256 blockLen0 = 1 << (st.logN - cfg.initialK + cfg.logInvRates[0]);
            st.openAt = cap0At;
            st.openLen = cap0Len;
            (Consistency memory cn, uint256 enforced) = levelOpen(st, cfg, 0, blockLen0, 1 << cfg.initialK, st.initial);
            introduce(st, cn, enforced, cfg.claimBits[1], st.logN - cfg.initialK, 0);
        }
        Meter.mark(11);
        st.prevLanes = cfg.recursiveKs[0];
        st.prevCols = st.splitDim - st.prevLanes;
        st.prevRate = cfg.logInvRates[1];
        for (uint256 i = 0; i < cfg.steps; ++i) {
            st.levels[i] = sumcheck(st, cfg.recursiveKs[i]);
            uint256 ext = st.splitDim - cfg.recursiveKs[i];
            uint256 blockLen = 1 << (st.prevCols + st.prevRate);
            if (i + 1 == cfg.steps) {
                finalLevel(st, cfg, i, ext, blockLen, sw);
                return;
            }
            recursiveLevel(st, cfg, i, ext, blockLen);
            Meter.mark(12 + i);
        }
    }

    function recursiveLevel(LigeritoState memory st, LigeritoConfig memory cfg, uint256 i, uint256 ext, uint256 blockLen)
        internal
        view
    {
        st.openAt = st.capAt;
        st.openLen = st.capLen;
        st.splitDim = ext + 1;
        readCap(st, cfg.depths[i + 2][0]);
        ood(st, cfg, i + 2, st.splitDim, i + 1, true);
        (Consistency memory cn, uint256 enforced) = levelOpen(st, cfg, i + 1, blockLen, 1 << st.prevLanes, st.levels[i]);
        introduce(st, cn, enforced, cfg.claimBits[i + 2], ext, i + 1);
        st.prevLanes = cfg.recursiveKs[i + 1];
        st.prevCols = st.splitDim - st.prevLanes;
        st.prevRate = cfg.logInvRates[i + 2];
    }

    function finalLevel(
        LigeritoState memory st,
        LigeritoConfig memory cfg,
        uint256 i,
        uint256 ext,
        uint256 blockLen,
        Switched memory sw
    ) internal {
        uint256 yrAt = st.p;
        for (uint256 j = 0; j < (2 << ext); ++j) {
            Transcript.observe(st.tr, Calldata.f128(yrAt + 16 * j));
        }
        st.p += 32 << ext;
        st.openAt = st.capAt;
        st.openLen = st.capLen;
        (Consistency memory last, uint256 enforced) = levelOpen(st, cfg, i + 1, blockLen, 1 << st.prevLanes, st.levels[i]);
        last.beta = Transcript.powSample(st.tr, Calldata.nonce(st.p), cfg.claimBits[i + 1]);
        st.p += 8;
        st.claim ^= GF2.mul256By128(enforced, last.beta);
        last.logCols = ext;
        last.start = cfg.steps;
        st.cons[st.nCons++] = last;
        if (st.p != st.end) revert Trailing();
        Meter.mark(20);
        uint256[] memory original = originalChallenges(st, 0, true);
        uint256[] memory mu = weightsOf(yrAt, ext);
        uint256 got = GF2.mul256(
            Residual.ringSwitch(original, _points(sw.claims), sw.eqs, sw.gammas, mu), factorProduct(st, 0)
        );
        Meter.mark(21);
        got ^= oodDot(st, original, ext, mu);
        Meter.mark(22);
        got ^= consistencyDot(st, mu);
        Meter.mark(23);
        if (got != st.claim) revert ResidualMismatch();
    }

    /// `Σ_y μ_y·O[y]` for `O` the out-of-domain part of the residual.
    function oodDot(LigeritoState memory st, uint256[] memory original, uint256 ext, uint256[] memory mu)
        internal
        pure
        returns (uint256 got)
    {
        uint256[] memory residual = new uint256[](1 << ext);
        for (uint256 o = 0; o < st.nOod; ++o) {
            Ood memory od = st.oods[o];
            uint256[] memory fixedPart;
            uint256 scale;
            if (od.split == type(uint256).max) {
                fixedPart = original;
                scale = factorProduct(st, 0);
            } else {
                fixedPart = splitChallenges(st, od.split);
                scale = factorProduct(st, od.split + 1);
            }
            uint256[] memory values = eqResidual(od.point, fixedPart, ext, GF2.mul256By128(scale, od.beta));
            for (uint256 y = 0; y < residual.length; ++y) {
                residual[y] ^= values[y];
            }
        }
        for (uint256 y = 0; y < residual.length; ++y) {
            got ^= GF2.mul256(residual[y], mu[y]);
        }
    }

    function _points(Claim[] memory claims) internal pure returns (uint256[][] memory xs) {
        xs = new uint256[][](claims.length);
        for (uint256 c = 0; c < claims.length; ++c) {
            xs[c] = claims[c].x;
        }
    }

    /// `μ_y = yr[2y] + u·yr[2y+1]`: the final check's weight on residual point `y`.
    function weightsOf(uint256 yrAt, uint256 ext) internal pure returns (uint256[] memory mu) {
        mu = new uint256[](1 << ext);
        for (uint256 y = 0; y < mu.length; ++y) {
            mu[y] = (Calldata.f128(yrAt + 32 * y + 16) << 128) | Calldata.f128(yrAt + 32 * y);
        }
    }

    /// `Σ_y μ_y·C[y]` for `C` the consistency part of the residual.
    function consistencyDot(LigeritoState memory st, uint256[] memory mu) internal pure returns (uint256 got) {
        for (uint256 c = 0; c < st.nCons; ++c) {
            Consistency memory cn = st.cons[c];
            uint256[] memory fixedPart = originalChallenges(st, cn.start, false);
            uint256 value = Residual.consistency(cn.logCols, cn.queries, GF2.eqTable(cn.alpha), fixedPart, mu);
            got ^= GF2.mul256(value, GF2.mul256By128(factorProduct(st, cn.start), cn.beta));
        }
    }

    function originalChallenges(LigeritoState memory st, uint256 start, bool withInitial)
        internal
        pure
        returns (uint256[] memory out)
    {
        bool initial = withInitial && start == 0;
        uint256 len = initial ? st.initial.length : 0;
        for (uint256 l = start; l < st.levels.length; ++l) {
            len += st.levels[l].length - 1;
        }
        out = new uint256[](len);
        uint256 at;
        if (initial) {
            for (uint256 k = 0; k < st.initial.length; ++k) {
                out[at++] = st.initial[k];
            }
        }
        for (uint256 l = start; l < st.levels.length; ++l) {
            for (uint256 k = 1; k < st.levels[l].length; ++k) {
                out[at++] = st.levels[l][k];
            }
        }
    }

    function splitChallenges(LigeritoState memory st, uint256 split) internal pure returns (uint256[] memory out) {
        uint256 len = st.levels[split].length;
        for (uint256 l = split + 1; l < st.levels.length; ++l) {
            len += st.levels[l].length - 1;
        }
        out = new uint256[](len);
        uint256 at;
        for (uint256 k = 0; k < st.levels[split].length; ++k) {
            out[at++] = st.levels[split][k];
        }
        for (uint256 l = split + 1; l < st.levels.length; ++l) {
            for (uint256 k = 1; k < st.levels[l].length; ++k) {
                out[at++] = st.levels[l][k];
            }
        }
    }

    function factorProduct(LigeritoState memory st, uint256 start) internal pure returns (uint256 acc) {
        acc = 1;
        uint256 onePlusU = (uint256(1) << 128) | 1;
        for (uint256 l = start; l < st.levels.length; ++l) {
            acc = GF2.mul256(acc, 1 ^ GF2.mul256(st.levels[l][0], onePlusU));
        }
    }

    function eqResidual(uint256[] memory point, uint256[] memory fixedPart, uint256 ext, uint256 scale)
        internal
        pure
        returns (uint256[] memory out)
    {
        uint256 f = fixedPart.length;
        uint256 prefix = scale;
        for (uint256 j = 0; j < f; ++j) {
            prefix = GF2.mul256(prefix, 1 ^ point[j] ^ fixedPart[j]);
        }
        out = new uint256[](1 << ext);
        for (uint256 y = 0; y < out.length; ++y) {
            uint256 s = 1;
            for (uint256 j = 0; j < ext; ++j) {
                uint256 z = point[f + j];
                s = GF2.mul(s, (y >> j) & 1 == 1 ? z : 1 ^ z);
            }
            out[y] = GF2.mul256By128(prefix, s);
        }
    }
}
