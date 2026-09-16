// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "./Calldata.sol";
import {Constants} from "./Constants.sol";
import {FiatShamir} from "./FiatShamir.sol";
import {GF2} from "./GF2.sol";
import {Meter} from "./Meter.sol";
import {Opening} from "./Opening.sol";
import {Claim, Piop} from "./Piop.sol";
import {Transcript} from "./Transcript.sol";

/// The verifier of a lift's matrix proof for one pinned statement: that the explicit rows' share
/// of every chunk's matrix claim is the table-weighted sum of the statement's committed entry list
/// (see `crates/lift/src/matrix.rs`).
contract FlockMatrix {
    bytes internal constant LIFT_VERSION = "pofseed-flock-lift-v1";
    uint256 internal constant M = 28;
    uint256 internal constant LOG_LEN = 22;
    uint256 internal constant CLAIM_WORDS = 112;
    uint256 internal constant MAIN_DEGREE = 8;
    uint256 internal constant COUNT_DEGREE = 15;
    uint256 internal constant COUNTS = 9474;
    uint256 internal constant ADDRESS_BITS = 59;
    uint256 internal constant P_AT = 1154;
    uint256 internal constant P_COLS = 65;

    /// Keccak-256 of the committed entry list's cap, as it sits in calldata.
    bytes32 public immutable capHash;
    /// Whether the entry list is opened under Ligerito's `Slim` profile rather than `Fast`.
    bool public immutable slim;

    error Shape();
    error EntryCommitment();
    error MainSumcheck();
    error CountSumcheck();

    constructor(bytes32 capHash_, bool slim_) {
        capHash = capHash_;
        slim = slim_;
    }

    /// The running state of one verification.
    struct St {
        uint256 tr;
        uint256 p;
        uint256 n;
        uint256 claim;
        uint256 countsAt;
        uint256[] weights;
        uint256[] alpha;
        uint256[][] skip;
        uint256[][] zp;
        uint256[][] x;
        uint256[][] r;
        uint256[] rho;
        uint256[] sigma;
        uint256[] gammas;
        uint256[][] points;
    }

    /// Verifies the matrix proof `proof` of the lift whose statement digest is `digest`, for the
    /// flattened matrix claims `claims` of its chunks and their structured parts `parts`.
    function verify(uint256[] calldata claims, uint256[] calldata parts, bytes32 digest, bytes calldata proof)
        external
        returns (bool)
    {
        Meter.mark(300);
        uint256 n = claims.length / CLAIM_WORDS;
        if (n == 0 || claims.length != n * CLAIM_WORDS || parts.length != 64 * n) revert Shape();
        St memory st;
        st.n = n;
        uint256 capAt = _offset(proof);
        uint256 capLen = 1 << Constants.ligerito(M, slim).depths[0][0];
        if (_hashAt(capAt, 32 * capLen) != capHash) revert EntryCommitment();
        st.p = capAt + 32 * capLen;
        st.tr = Transcript.createFromMemorySized(
            abi.encodePacked(LIFT_VERSION, digest, "committed-matrix"), COUNTS * 16 + 4096
        );
        _claims(st, claims, parts);
        Meter.mark(301);
        _main(st);
        Meter.mark(302);
        _counts(st);
        Meter.mark(303);
        _countSumcheck(st);
        Meter.mark(304);
        Claim[] memory opened = new Claim[](1);
        opened[0] = _bits(st);
        Meter.mark(305);
        Opening.verify(
            st.tr, Constants.PHI8, st.p, capAt + proof.length, Constants.ligerito(M, slim), M, capAt, capLen, opened
        );
        Meter.mark(306);
        return true;
    }

    function _claims(St memory st, uint256[] calldata claims, uint256[] calldata parts) private pure {
        uint256 n = st.n;
        st.alpha = new uint256[](n);
        st.skip = new uint256[][](n);
        st.zp = new uint256[][](n);
        st.x = new uint256[][](n);
        st.r = new uint256[][](n);
        uint256[] memory values = new uint256[](n);
        Transcript.label(st.tr, Constants.L_MATRIX_0, Constants.L_MATRIX_1, Constants.L_MATRIX_LEN);
        Transcript.header(st.tr, 5, 0, 8);
        _word16(st.tr, FiatShamir.uint64le(n) << 64);
        for (uint256 c = 0; c < n; ++c) {
            uint256 b = c * CLAIM_WORDS;
            st.alpha[c] = claims[b];
            st.skip[c] = Piop.lagrange(Constants.PHI8, claims[b + 2]);
            st.x[c] = _slice(claims, b + 4, LOG_LEN);
            st.r[c] = _slice(claims, b + 26, LOG_LEN);
            st.zp[c] = _slice(claims, b + 48, 64);
            uint256 v = claims[b + 3];
            for (uint256 s = 0; s < 64; ++s) {
                v ^= GF2.mul(st.zp[c][s], parts[64 * c + s]);
            }
            values[c] = v;
            Transcript.observe(st.tr, st.alpha[c]);
            Transcript.observeSlice(st.tr, st.skip[c]);
            Transcript.observeSlice(st.tr, st.zp[c]);
            Transcript.observeSlice(st.tr, st.x[c]);
            Transcript.observeSlice(st.tr, st.r[c]);
            Transcript.observe(st.tr, v);
        }
        uint256 mu = Transcript.powSample(st.tr, Calldata.nonce(st.p), 2);
        st.p += 8;
        st.weights = new uint256[](n);
        uint256 w = 1;
        for (uint256 c = 0; c < n; ++c) {
            st.weights[c] = w;
            st.claim ^= GF2.mul(w, values[c]);
            w = GF2.mul(w, mu);
        }
    }

    /// Appends the sixteen high bytes of `w` to the pending transcript bytes.
    function _word16(uint256 tr, uint256 w) private pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), shl(128, w))
            mstore(add(tr, 0x20), add(l, 16))
        }
    }

    /// One sumcheck of `rounds` rounds whose messages carry `degree` coefficients, returning the
    /// challenges and leaving the final claim in `st.claim`.
    function _sumcheck(St memory st, uint256 degree, uint256 bits) private pure returns (uint256[] memory rs) {
        rs = new uint256[](LOG_LEN);
        for (uint256 i = 0; i < LOG_LEN; ++i) {
            Transcript.observeSliceFromCalldata(st.tr, st.p, degree);
            uint256 msgAt = st.p;
            st.p += 16 * degree;
            uint256 r = Transcript.powSample(st.tr, Calldata.nonce(st.p), bits);
            st.p += 8;
            rs[i] = r;
            st.claim = _round(msgAt, degree, st.claim, r);
        }
    }

    /// `g(r)` for the round polynomial with coefficients `m0, c1, m1, …` where `c1` makes
    /// `g(0) + g(1)` equal `claim`.
    function _round(uint256 at, uint256 degree, uint256 claim, uint256 r) private pure returns (uint256 acc) {
        uint256 higher;
        for (uint256 k = 1; k < degree; ++k) {
            higher ^= Calldata.f128(at + 16 * k);
        }
        for (uint256 k = degree - 1; k >= 1; --k) {
            acc = GF2.mul(acc, r) ^ Calldata.f128(at + 16 * k);
        }
        acc = GF2.mul(acc, r) ^ claim ^ higher;
        acc = GF2.mul(acc, r) ^ Calldata.f128(at);
    }

    function _main(St memory st) private pure {
        st.rho = _sumcheck(st, MAIN_DEGREE, 3);
        st.countsAt = st.p;
        st.p += 16 * COUNTS;
        uint256[] memory suffix = _suffix(st.countsAt + 16 * P_AT);
        uint256 expected;
        for (uint256 c = 0; c < st.n; ++c) {
            uint256 term = GF2.mul(st.weights[c], _sideDot(st, c));
            term = GF2.mul(term, _chunkDots(st.countsAt, st.x[c], 2));
            term = GF2.mul(term, _chunkDots(st.countsAt, st.r[c], 578));
            term = GF2.mul(term, _prefixDot(suffix, st.skip[c], st.zp[c]));
            expected ^= term;
        }
        if (expected != st.claim) revert MainSumcheck();
    }

    function _sideDot(St memory st, uint256 c) private pure returns (uint256) {
        return GF2.mul(st.alpha[c], Calldata.f128(st.countsAt)) ^ Calldata.f128(st.countsAt + 16);
    }

    /// The product of the three word-chunk lookups' weighted counts, the counts starting at
    /// lookup offset `from`, under the `eq` tables of `point`'s 8-, 8- and 6-coordinate pieces.
    function _chunkDots(uint256 countsAt, uint256[] memory point, uint256 from) private pure returns (uint256 acc) {
        acc = 1;
        uint256 at = countsAt + 16 * from;
        uint256[3] memory widths = [uint256(8), 8, 6];
        uint256 start;
        for (uint256 k = 0; k < 3; ++k) {
            uint256[] memory piece = new uint256[](widths[k]);
            for (uint256 i = 0; i < widths[k]; ++i) {
                piece[i] = point[start + i];
            }
            start += widths[k];
            acc = GF2.mul(acc, _dotAt(GF2.eqTable(piece), at));
            at += 16 << widths[k];
        }
    }

    /// `Σ t[i]·counts[i]` over the table `t`, with the counts at `at`.
    function _dotAt(uint256[] memory t, uint256 at) private pure returns (uint256 acc) {
        uint256 len = t.length;
        for (uint256 i = 0; i < len; ++i) {
            acc ^= GF2.mul(t[i], Calldata.f128(at + 16 * i));
        }
    }

    /// `S[u][t] = Σ_{j > t} ĉ_P[u][j]` for 128 rows and 64 bit positions, row-major.
    function _suffix(uint256 at) private pure returns (uint256[] memory s) {
        s = new uint256[](128 * 64);
        for (uint256 u = 0; u < 128; ++u) {
            uint256 row = at + 16 * u * P_COLS;
            uint256 acc;
            for (uint256 t = 64; t > 0; --t) {
                acc ^= Calldata.f128(row + 16 * t);
                s[u * 64 + t - 1] = acc;
            }
        }
    }

    /// `Σ_{u,j} ĉ_P[u][j]·P[u][j]` from the suffix sums: `Σ_t skip[t]·Σ_v z[v]·(S[(v − t) mod 64][t] + S[64 + v][t])`.
    function _prefixDot(uint256[] memory s, uint256[] memory skip, uint256[] memory z) private pure returns (uint256 acc) {
        for (uint256 t = 0; t < 64; ++t) {
            uint256 inner;
            for (uint256 v = 0; v < 64; ++v) {
                uint256 m = s[((v + 64 - t) & 63) * 64 + t] ^ s[(64 + v) * 64 + t];
                inner ^= GF2.mul(z[v], m);
            }
            acc ^= GF2.mul(skip[t], inner);
        }
    }

    function _counts(St memory st) private pure {
        Transcript.observeSliceFromCalldata(st.tr, st.countsAt, COUNTS);
        uint256 gamma = Transcript.powSample(st.tr, Calldata.nonce(st.p), 5);
        st.p += 8;
        uint256[8] memory widths = [uint256(1), 8, 8, 6, 8, 8, 6, 14];
        st.points = new uint256[][](8);
        st.gammas = new uint256[](8);
        uint256 g = 1;
        for (uint256 l = 0; l < 8; ++l) {
            st.points[l] = Transcript.sampleVec(st.tr, widths[l]);
            st.gammas[l] = g;
            g = GF2.mul(g, gamma);
        }
        uint256 claim;
        uint256 at = st.countsAt;
        for (uint256 l = 0; l < 7; ++l) {
            uint256[] memory eq = GF2.eqTable(st.points[l]);
            claim ^= GF2.mul(st.gammas[l], _dotAt(eq, at));
            at += 16 << widths[l];
        }
        claim ^= GF2.mul(st.gammas[7], _prefixCount(st.points[7], at));
        st.claim = claim;
    }

    /// `Σ_{u,j} eq(r_hi, u)·eq(r_lo, j)·ĉ_P[u][j]`.
    function _prefixCount(uint256[] memory point, uint256 at) private pure returns (uint256 acc) {
        uint256[] memory lo = new uint256[](7);
        uint256[] memory hi = new uint256[](7);
        for (uint256 i = 0; i < 7; ++i) {
            lo[i] = point[i];
            hi[i] = point[7 + i];
        }
        uint256[] memory eqLo = GF2.eqTable(lo);
        uint256[] memory eqHi = GF2.eqTable(hi);
        for (uint256 u = 0; u < 128; ++u) {
            uint256 row;
            uint256 base = at + 16 * u * P_COLS;
            for (uint256 j = 0; j < P_COLS; ++j) {
                row ^= GF2.mul(eqLo[j], Calldata.f128(base + 16 * j));
            }
            acc ^= GF2.mul(eqHi[u], row);
        }
    }

    function _countSumcheck(St memory st) private pure {
        st.sigma = _sumcheck(st, COUNT_DEGREE, 4);
    }

    function _bits(St memory st) private pure returns (Claim memory opened) {
        uint256 bitsAt = st.p;
        st.p += 16 * ADDRESS_BITS;
        uint256 eq = 1;
        for (uint256 i = 0; i < LOG_LEN; ++i) {
            eq = GF2.mul(eq, 1 ^ st.rho[i] ^ st.sigma[i]);
        }
        uint256[8] memory offsets = [uint256(0), 1, 9, 17, 23, 31, 39, 45];
        uint256 sum;
        for (uint256 l = 0; l < 8; ++l) {
            uint256 prod = st.gammas[l];
            uint256[] memory point = st.points[l];
            for (uint256 i = 0; i < point.length; ++i) {
                prod = GF2.mul(prod, 1 ^ point[i] ^ Calldata.f128(bitsAt + 16 * (offsets[l] + i)));
            }
            sum ^= prod;
        }
        if (GF2.mul(eq, sum) != st.claim) revert CountSumcheck();
        Transcript.observeSliceFromCalldata(st.tr, bitsAt, ADDRESS_BITS);
        uint256 zeta = Transcript.powSample(st.tr, Calldata.nonce(st.p), 6);
        st.p += 8;
        uint256[] memory w = Piop.lagrange(Constants.PHI8, zeta);
        uint256 value;
        for (uint256 i = 0; i < ADDRESS_BITS; ++i) {
            value ^= GF2.mul(w[i], Calldata.f128(bitsAt + 16 * i));
        }
        opened = Claim(zeta, st.sigma, value);
    }

    function _slice(uint256[] calldata v, uint256 from, uint256 len) private pure returns (uint256[] memory out) {
        out = new uint256[](len);
        for (uint256 k = 0; k < len; ++k) {
            out[k] = v[from + k];
        }
    }

    function _hashAt(uint256 at, uint256 len) private pure returns (bytes32 h) {
        bytes memory b = new bytes(len);
        assembly ("memory-safe") {
            calldatacopy(add(b, 0x20), at, len)
            h := keccak256(add(b, 0x20), len)
        }
    }

    function _offset(bytes calldata b) private pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }
}
