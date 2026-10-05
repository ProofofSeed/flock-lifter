// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
import {W} from "./W.sol";
import {WrapKey} from "./WrapKey.sol";

/// What one WHIR opening is verified against: the commitment's schedule and cap, and the claimed
/// values of the committed polynomial at points over the base field.
struct WhirClaim {
    /// Per committed function: variables, folded variables, log domain, queries (two bytes),
    /// out-of-domain samples and log cap size.
    bytes rounds;
    /// Variables of the final polynomial.
    uint256 finalVars;
    /// Proof-of-work bits before each query phase.
    uint256 powBits;
    /// Where the commitment's cap sits in memory.
    uint256 cap;
    /// The points, each over every variable.
    uint256[][] points;
    /// The values at the points.
    uint256[] values;
}

/// The verifier's running state.
struct WhirState {
    uint256 tr;
    uint256 p;
    uint256 claim;
    /// Every sumcheck challenge, in order.
    uint256[] challenges;
    uint256 count;
    /// The equality terms of the final weight: their points, over the last variables, and their
    /// coefficients.
    uint256[][] eqPoints;
    uint256[] eqCoeffs;
    uint256 eqCount;
    /// The queried positions of every committed function but the last, and their coefficients.
    uint256[][] positions;
    uint256[][] coeffs;
    /// The folding challenges of the function being queried, and its cap in memory.
    uint256[] alpha;
    uint256 cap;
}

/// The verifier of a WHIR opening over GF(2^128) with challenges in GF(2^256): codeword rows on
/// Keccak-256 trees, the folds' sumcheck, and the final weight in closed form.
library Whir {
    error MerklePath();
    error FinalPolynomial();
    error Sumcheck();

    // "flock-whir-open", then the byte string holding the number of points and of weights.
    uint256 internal constant L_OPEN_0 = 0x0200000000000000000000000000000f666c6f636b2d776869722d6f70656e00;

    function _round(bytes memory rounds, uint256 i)
        private
        pure
        returns (uint256 vars, uint256 fold, uint256 logDomain, uint256 queries, uint256 ood, uint256 capLog)
    {
        vars = W.read(rounds, 7 * i, 1);
        fold = W.read(rounds, 7 * i + 1, 1);
        logDomain = W.read(rounds, 7 * i + 2, 1);
        queries = W.read(rounds, 7 * i + 3, 2);
        ood = W.read(rounds, 7 * i + 5, 1);
        capLog = W.read(rounds, 7 * i + 6, 1);
    }

    /// `n` out-of-domain points of `vars` coordinates each.
    function _samplePoints(WhirState memory st, uint256 n, uint256 vars) private pure returns (uint256 first) {
        first = st.eqCount;
        for (uint256 k = 0; k < n; ++k) {
            uint256[] memory z = new uint256[](vars);
            for (uint256 i = 0; i < vars; ++i) {
                z[i] = W.sample256(st.tr);
            }
            st.eqPoints[st.eqCount++] = z;
        }
    }

    /// Runs `n` sumcheck rounds.
    function _sumcheck(WhirState memory st, uint256 n) private pure returns (uint256[] memory alpha) {
        alpha = new uint256[](n);
        uint256 tr = st.tr;
        uint256 p = st.p;
        uint256 claim = st.claim;
        for (uint256 i = 0; i < n; ++i) {
            uint256 e1 = Calldata.f256(p);
            uint256 einf = Calldata.f256(p + 32);
            p += 64;
            W.observe256(tr, e1);
            W.observe256(tr, einf);
            uint256 r = W.sample256(tr);
            claim = claim ^ e1 ^ F.mul256(claim ^ einf ^ F.mul256(einf, r), r);
            alpha[i] = r;
            st.challenges[st.count++] = r;
        }
        st.p = p;
        st.claim = claim;
    }

    /// The equality table of extension elements `point`, lowest coordinate first.
    function _eqTable256(uint256[] memory point) private pure returns (uint256[] memory t) {
        uint256 d = point.length;
        t = new uint256[](1 << d);
        t[0] = 1;
        for (uint256 j = 0; j < d; ++j) {
            uint256 half = 1 << j;
            uint256 x = point[j];
            for (uint256 i = 0; i < half; ++i) {
                uint256 lo = t[i];
                uint256 hi = F.mul256(lo, x);
                t[i + half] = hi;
                t[i] = lo ^ hi;
            }
        }
    }

    /// Reads the opened rows of committed function `index` at the positions `words` select, checks
    /// them under its cap, and returns the positions with the folded values there.
    function _openings(WhirState memory st, bytes memory rounds, uint256 index, uint256[] memory words)
        private
        pure
        returns (uint256[] memory positions, uint256[] memory folded)
    {
        (, uint256 fold, uint256 logDomain, uint256 queries,, uint256 capLog) = _round(rounds, index);
        uint256 width = index == 0 ? 16 : 32;
        uint256 rowBytes = width << fold;
        uint256[] memory eq = _eqTable256(st.alpha);
        positions = new uint256[](queries);
        folded = new uint256[](queries);
        uint256 rowsAt = st.p;
        uint256 pathsAt = rowsAt + queries * rowBytes;
        uint256 depth = logDomain - capLog;
        for (uint256 q = 0; q < queries; ++q) {
            uint256 pos = words[q] & ((1 << logDomain) - 1);
            positions[q] = pos;
            uint256 rowAt = rowsAt + q * rowBytes;
            if (_root(rowAt, rowBytes, pathsAt + 32 * depth * q, depth, pos) != _capEntry(st.cap, pos >> depth)) revert MerklePath();
            uint256 acc;
            if (index == 0) {
                for (uint256 l = 0; l < eq.length; ++l) {
                    acc ^= F.mul256By128(eq[l], Calldata.f128(rowAt + 16 * l));
                }
            } else {
                for (uint256 l = 0; l < eq.length; ++l) {
                    uint256 v = Calldata.f256(rowAt + 32 * l);
                    acc ^= F.mul256(eq[l], (v << 128) | (v >> 128));
                }
            }
            folded[q] = acc;
        }
        st.p = pathsAt + 32 * depth * queries;
    }

    function _capEntry(uint256 cap, uint256 i) private pure returns (bytes32 h) {
        assembly ("memory-safe") {
            h := mload(add(cap, shl(5, i)))
        }
    }

    /// The node `depth` levels above leaf `pos`, whose row is the `len` calldata bytes at `rowAt`
    /// and whose path is at `pathAt`.
    function _root(uint256 rowAt, uint256 len, uint256 pathAt, uint256 depth, uint256 pos) private pure returns (bytes32 node) {
        assembly ("memory-safe") {
            let buf := mload(0x40)
            mstore8(buf, 0)
            calldatacopy(add(buf, 1), rowAt, len)
            node := keccak256(buf, add(len, 1))
            mstore8(buf, 1)
            for { let l := 0 } lt(l, depth) { l := add(l, 1) } {
                let sibling := calldataload(add(pathAt, shl(5, l)))
                switch and(shr(l, pos), 1)
                case 0 {
                    mstore(add(buf, 1), node)
                    mstore(add(buf, 33), sibling)
                }
                default {
                    mstore(add(buf, 1), sibling)
                    mstore(add(buf, 33), node)
                }
                node := keccak256(buf, 65)
            }
        }
    }

    /// Copies a cap of `2^capLog` hashes from calldata into memory, observing it.
    function _readCap(WhirState memory st, uint256 capLog) private pure {
        uint256 len = 32 << capLog;
        Transcript.header(st.tr, 5, 0, len);
        W.appendCalldata(st.tr, st.p, len);
        uint256 cap;
        uint256 p = st.p;
        assembly ("memory-safe") {
            cap := mload(0x40)
            mstore(0x40, add(cap, len))
            calldatacopy(cap, p, len)
        }
        st.cap = cap;
        st.p = p + len;
    }

    /// Verifies the opening at calldata `p` of the claim `c`, on the transcript `tr` that has
    /// absorbed the commitment; returns the cursor after it.
    function verify(uint256 tr, WhirClaim memory c, uint256 p) internal pure returns (uint256) {
        WhirState memory st;
        st.tr = tr;
        st.p = p;
        uint256 n = c.rounds.length / 7;
        (uint256 m,,,, uint256 ood,) = _round(c.rounds, 0);
        {
            uint256 terms = c.points.length;
            for (uint256 i = 0; i < n; ++i) {
                terms += W.read(c.rounds, 7 * i + 5, 1);
            }
            st.eqPoints = new uint256[][](terms);
            st.eqCoeffs = new uint256[](terms);
            st.challenges = new uint256[](m);
            st.positions = new uint256[][](n);
            st.coeffs = new uint256[][](n);
        }
        st.cap = c.cap;
        _samplePoints(st, ood, m);
        _start(st, c, ood);
        st.alpha = _sumcheck(st, W.read(c.rounds, 1, 1));
        for (uint256 i = 1; i < n; ++i) {
            _fold(st, c, i);
        }
        _finish(st, c, n);
        return st.p;
    }

    /// Binds the claims, batches them with the out-of-domain answers, and starts the claim.
    function _start(WhirState memory st, WhirClaim memory c, uint256 ood) private pure {
        uint256 tr = st.tr;
        uint256 oodAt = st.p;
        for (uint256 k = 0; k < ood; ++k) {
            W.observe256(tr, Calldata.f256(oodAt + 32 * k));
        }
        st.p = oodAt + 32 * ood;
        Transcript.label(tr, L_OPEN_0, 0, 32);
        uint256 np = c.points.length;
        Transcript.header(tr, 5, 0, 16);
        // The number of points, then of weights, as little-endian 64-bit integers.
        Transcript.raw(tr, bytes32(_le64(np) << 192));
        assembly ("memory-safe") {
            mstore(add(tr, 0x20), sub(mload(add(tr, 0x20)), 16))
        }
        for (uint256 k = 0; k < np; ++k) {
            uint256[] memory z = c.points[k];
            for (uint256 i = 0; i < z.length; ++i) {
                W.observe256(tr, z[i]);
            }
            W.observe256(tr, c.values[k]);
            st.eqPoints[st.eqCount++] = z;
        }
        uint256 gamma = W.sample256(tr);
        uint256 power = gamma;
        uint256 claim;
        for (uint256 k = 0; k < ood + np; ++k) {
            st.eqCoeffs[k] = power;
            claim ^= k < ood ? F.mul256(power, Calldata.f256(oodAt + 32 * k)) : F.mul256By128(power, c.values[k - ood]);
            power = F.mul256(power, gamma);
        }
        st.claim = claim;
    }

    function _le64(uint256 v) private pure returns (uint256 r) {
        for (uint256 i = 0; i < 8; ++i) {
            r |= ((v >> (8 * i)) & 0xff) << (8 * (7 - i));
        }
    }

    /// One folded function: its cap and out-of-domain answers, the previous function's queries,
    /// and its sumcheck rounds.
    function _fold(WhirState memory st, WhirClaim memory c, uint256 i) private pure {
        uint256 tr = st.tr;
        (uint256 vars, uint256 fold,,, uint256 ood, uint256 capLog) = _round(c.rounds, i);
        uint256 prevCap = st.cap;
        _readCap(st, capLog);
        uint256 nextCap = st.cap;
        uint256 first = _samplePoints(st, ood, vars);
        uint256 oodAt = st.p;
        for (uint256 k = 0; k < ood; ++k) {
            W.observe256(tr, Calldata.f256(oodAt + 32 * k));
        }
        st.p = oodAt + 32 * ood + 8;
        uint256[] memory words =
            Transcript.powSampleVec(tr, Calldata.nonce(oodAt + 32 * ood), c.powBits, W.read(c.rounds, 7 * (i - 1) + 3, 2));
        st.cap = prevCap;
        (uint256[] memory positions, uint256[] memory folded) = _openings(st, c.rounds, i - 1, words);
        st.cap = nextCap;
        uint256 gamma = W.sample256(tr);
        uint256 power = gamma;
        uint256 claim = st.claim;
        for (uint256 k = 0; k < ood; ++k) {
            st.eqCoeffs[first + k] = power;
            claim ^= F.mul256(power, Calldata.f256(oodAt + 32 * k));
            power = F.mul256(power, gamma);
        }
        uint256[] memory coeffs = new uint256[](folded.length);
        for (uint256 q = 0; q < folded.length; ++q) {
            coeffs[q] = power;
            claim ^= F.mul256(power, folded[q]);
            power = F.mul256(power, gamma);
        }
        st.positions[i - 1] = positions;
        st.coeffs[i - 1] = coeffs;
        st.claim = claim;
        st.alpha = _sumcheck(st, fold);
    }

    /// The final polynomial, the last function's queries against it, the last sumcheck rounds and
    /// the last equation.
    function _finish(WhirState memory st, WhirClaim memory c, uint256 n) private pure {
        uint256 tr = st.tr;
        uint256 size = 1 << c.finalVars;
        uint256[] memory poly = new uint256[](size);
        for (uint256 k = 0; k < size; ++k) {
            poly[k] = Calldata.f256(st.p + 32 * k);
            W.observe256(tr, poly[k]);
        }
        uint256 nonceAt = st.p + 32 * size;
        st.p = nonceAt + 8;
        (,, uint256 logDomain, uint256 queries,,) = _round(c.rounds, n - 1);
        uint256[] memory words = Transcript.powSampleVec(tr, Calldata.nonce(nonceAt), c.powBits, queries);
        (uint256[] memory positions, uint256[] memory folded) = _openings(st, c.rounds, n - 1, words);
        bytes memory sub = WrapKey.SUBSPACE;
        uint256[] memory v = new uint256[](size);
        for (uint256 q = 0; q < queries; ++q) {
            for (uint256 k = 0; k < size; ++k) {
                v[k] = poly[k];
            }
            uint256 len = size;
            for (uint256 i = 0; i < c.finalVars; ++i) {
                uint256 w = _coordinate(sub, positions[q], i, logDomain);
                len >>= 1;
                for (uint256 k = 0; k < len; ++k) {
                    v[k] = v[2 * k] ^ F.mul256By128(v[2 * k + 1], w);
                }
            }
            if (v[0] != folded[q]) revert FinalPolynomial();
        }
        uint256[] memory r = _sumcheck(st, c.finalVars);
        uint256 len2 = size;
        for (uint256 i = 0; i < c.finalVars; ++i) {
            len2 >>= 1;
            for (uint256 k = 0; k < len2; ++k) {
                poly[k] = poly[2 * k] ^ F.mul256(r[i], poly[2 * k] ^ poly[2 * k + 1]);
            }
        }
        if (st.claim != F.mul256(poly[0], _weight(st, c, sub, n))) revert Sumcheck();
    }

    /// The novel-basis coordinate `Ŵ_i` of the domain's point `pos`.
    function _coordinate(bytes memory sub, uint256 pos, uint256 i, uint256 logDomain) private pure returns (uint256 acc) {
        acc = (pos >> i) & 1;
        for (uint256 j = i + 1; j < logDomain; ++j) {
            if ((pos >> j) & 1 == 1) acc ^= W.entry(sub, 32 * i + j, 16);
        }
    }

    /// The final weight at the sumcheck's point: every equality term, and every queried position's
    /// term `Π_i (1 + y_i·(1 + Ŵ_i(position)))`.
    function _weight(WhirState memory st, WhirClaim memory c, bytes memory sub, uint256 n) private pure returns (uint256 weight) {
        uint256 m = st.challenges.length;
        for (uint256 k = 0; k < st.eqCount; ++k) {
            uint256[] memory z = st.eqPoints[k];
            uint256 from = m - z.length;
            uint256 acc = st.eqCoeffs[k];
            for (uint256 i = 0; i < z.length; ++i) {
                acc = F.mul256(acc, 1 ^ z[i] ^ st.challenges[from + i]);
            }
            weight ^= acc;
        }
        for (uint256 r = 0; r + 1 < n; ++r) {
            uint256 vars = W.read(c.rounds, 7 * (r + 1), 1);
            uint256 logDomain = W.read(c.rounds, 7 * r + 2, 1);
            // `y_i·Ŵ_i(x^j)` at `[i·logDomain + j]`, for `j ≥ i`.
            uint256[] memory table = new uint256[](vars * logDomain);
            for (uint256 i = 0; i < vars; ++i) {
                uint256 y = st.challenges[m - vars + i];
                table[i * logDomain + i] = y;
                for (uint256 j = i + 1; j < logDomain; ++j) {
                    table[i * logDomain + j] = F.mul256By128(y, W.entry(sub, 32 * i + j, 16));
                }
            }
            uint256[] memory positions = st.positions[r];
            uint256[] memory coeffs = st.coeffs[r];
            for (uint256 q = 0; q < positions.length; ++q) {
                uint256 pos = positions[q];
                uint256 acc = coeffs[q];
                for (uint256 i = 0; i < vars; ++i) {
                    uint256 u = 1 ^ st.challenges[m - vars + i];
                    for (uint256 j = i; j < logDomain; ++j) {
                        if ((pos >> j) & 1 == 1) u ^= table[i * logDomain + j];
                    }
                    acc = F.mul256(acc, u);
                }
                weight ^= acc;
            }
        }
    }
}
