// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Constants} from "../Constants.sol";
import {FiatShamir} from "../FiatShamir.sol";
import {GF2} from "../GF2.sol";
import {Piop} from "../Piop.sol";
import {Transcript} from "../Transcript.sol";
import {Config} from "./Config.sol";
import {IStage, Staged, State} from "./Staged.sol";

/// The matrix proof's own stages, for one pinned entry commitment (as `FlockMatrix`): the cap,
/// the claims' batching and main sumcheck, its final check in items, the counts' claim with its
/// prefix part in rows, and the count sumcheck with the address bits, leading into the opening.
contract MatrixStages is IStage {
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
    uint256 internal constant ROUNDS = 26;
    uint256 internal constant DOT_ITEMS = 9;

    /// Keccak-256 of the committed entry list's cap, as it sits in calldata.
    bytes32 public immutable capHash;
    /// Whether the entry list is opened under Ligerito's `Slim` profile rather than `Fast`.
    bool public immutable slim;
    /// The first Keccak-f sub-block of the statement's block.
    uint256 public immutable firstKeccak;
    /// The Keccak-f sub-blocks of the statement's block.
    uint256 public immutable keccakSubs;

    error Shape();
    error EntryCommitment();
    error MainSumcheck();
    error CountSumcheck();
    error Counts();
    error Final();

    constructor(bytes32 capHash_, bool slim_, uint256 firstKeccak_, uint256 keccakSubs_) {
        capHash = capHash_;
        slim = slim_;
        firstKeccak = firstKeccak_;
        keccakSubs = keccakSubs_;
    }

    /// The first state of the matrix verification of the lift with statement digest `digest`,
    /// for its packed matrix claims `claims`.
    function start(bytes32 digest, uint256[] calldata claims) external view returns (bytes memory, uint256[] memory) {
        uint256 n = claims.length / CLAIM_WORDS;
        if (n == 0 || claims.length != n * CLAIM_WORDS) revert Shape();
        State memory st = Staged.fresh(2);
        st.v[Staged.DIGEST] = uint256(digest);
        st.v[Staged.N] = n;
        st.v[Staged.M] = M;
        st.v[Staged.SLIM] = slim ? 1 : 0;
        st.v[Staged.FIRST_KECCAK] = firstKeccak;
        st.v[Staged.KECCAK_SUBS] = keccakSubs;
        st.a[Staged.PACKED] = claims;
        uint256[] memory skips = new uint256[](64 * n);
        for (uint256 c = 0; c < n; ++c) {
            uint256[] memory skip = Piop.lagrange(Constants.PHI8, claims[c * CLAIM_WORDS + 2]);
            for (uint256 u = 0; u < 64; ++u) {
                skips[64 * c + u] = skip[u];
            }
        }
        st.a[Staged.SKIPS] = skips;
        Config.fill(st, M, slim);
        Staged.enter(st, Staged.M_START, 1);
        return (Staged.save(st), Staged.request(st, Staged.want1(Staged.PROOF, 0, 0, _capLen(st) * 32)));
    }

    function _capLen(State memory st) private pure returns (uint256) {
        return 1 << Config.capDepth(st, 0);
    }

    function run(bytes calldata state, uint256 upto, bytes calldata data)
        external
        view
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.M_START, Staged.M_CHECK);
        uint256 stage = st.v[Staged.STAGE];
        uint256 p = Staged.offset(data);
        uint256[] memory streams;
        if (stage == Staged.M_START) {
            _start(st, data);
        } else if (stage == Staged.M_MAIN) {
            streams = _main(st, p);
        } else if (stage == Staged.M_DOTS) {
            streams = _dots(st, upto, data);
        } else if (stage == Staged.M_COUNTS) {
            streams = _counts(st, data);
        } else if (stage == Staged.M_PREFIX) {
            streams = _prefix(st, upto, data);
        } else if (stage == Staged.M_BITS) {
            _bits(st, p);
            streams = Staged.sequential(st.v[Staged.POS]);
        } else {
            return _check(st);
        }
        return (Staged.save(st), Staged.request(st, streams));
    }

    function _start(State memory st, bytes calldata data) private view {
        uint256 capLen = _capLen(st);
        if (data.length != capLen * 32) revert Shape();
        uint256 at = Staged.offset(data);
        if (Staged.hashAt(at, capLen * 32) != capHash) revert EntryCommitment();
        st.a[Staged.CAP] = Staged.words(at, capLen);
        st.v[Staged.POS] = capLen * 32;
        uint256 tr = Transcript.createFromMemorySized(
            abi.encodePacked(LIFT_VERSION, bytes32(st.v[Staged.DIGEST]), "committed-matrix"), 1024
        );
        st.tr = Staged.keep(tr);
        st.a[Staged.VALUES] = new uint256[](st.v[Staged.N]);
        st.a[Staged.ACCS] = new uint256[](4 * st.v[Staged.N]);
        Staged.enter(st, Staged.STRUCT, ROUNDS * st.v[Staged.N]);
    }

    function _slice(uint256[] memory v, uint256 from, uint256 len) private pure returns (uint256[] memory out) {
        out = new uint256[](len);
        for (uint256 k = 0; k < len; ++k) {
            out[k] = v[from + k];
        }
    }

    function _word16(uint256 tr, uint256 w) private pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), shl(128, w))
            mstore(add(tr, 0x20), add(l, 16))
        }
    }

    /// Absorbs the claims, batches them and runs the main sumcheck.
    function _main(State memory st, uint256 p) private pure returns (uint256[] memory) {
        uint256 p0 = p;
        uint256 tr = Staged.restoreSized(st.tr, 1 << 16);
        uint256 n = st.v[Staged.N];
        uint256[] memory claims = st.a[Staged.PACKED];
        Transcript.label(tr, Constants.L_MATRIX_0, Constants.L_MATRIX_1, Constants.L_MATRIX_LEN);
        Transcript.header(tr, 5, 0, 8);
        _word16(tr, FiatShamir.uint64le(n) << 64);
        for (uint256 c = 0; c < n; ++c) {
            uint256 b = c * CLAIM_WORDS;
            Transcript.observe(tr, claims[b]);
            Transcript.observeSlice(tr, _slice(st.a[Staged.SKIPS], 64 * c, 64));
            Transcript.observeSlice(tr, _slice(claims, b + 48, 64));
            Transcript.observeSlice(tr, _slice(claims, b + 4, LOG_LEN));
            Transcript.observeSlice(tr, _slice(claims, b + 26, LOG_LEN));
            Transcript.observe(tr, st.a[Staged.VALUES][c]);
        }
        uint256 mu = Transcript.powSample(tr, Calldata.nonce(p), 2);
        p += 8;
        uint256[] memory weights = new uint256[](n);
        uint256 w = 1;
        uint256 claim;
        for (uint256 c = 0; c < n; ++c) {
            weights[c] = w;
            claim ^= GF2.mul(w, st.a[Staged.VALUES][c]);
            w = GF2.mul(w, mu);
        }
        st.a[Staged.WEIGHTS] = weights;
        st.a[Staged.ACCS] = new uint256[](n);
        st.v[Staged.CLAIM] = claim;
        (st.a[Staged.RHO], p) = _sumcheck(st, tr, p, MAIN_DEGREE, 3);
        uint256 countsAt = st.v[Staged.POS] + (p - p0);
        st.v[Staged.COUNTS_AT] = countsAt;
        st.v[Staged.READ] = countsAt;
        st.v[Staged.POS] = countsAt + 16 * COUNTS;
        st.tr = Staged.keep(tr);
        Staged.enter(st, Staged.M_DOTS, DOT_ITEMS * n);
        return _countStreams(st);
    }

    /// Both parts of the counts, whole, in every call.
    function _countStreams(State memory st) private pure returns (uint256[] memory) {
        uint256 at = st.v[Staged.COUNTS_AT];
        return Staged.want1(Staged.PROOF, at, 0, 16 * COUNTS);
    }

    function _sumcheck(State memory st, uint256 tr, uint256 p, uint256 degree, uint256 bits)
        private
        pure
        returns (uint256[] memory rs, uint256)
    {
        rs = new uint256[](LOG_LEN);
        for (uint256 i = 0; i < LOG_LEN; ++i) {
            Transcript.observeSliceFromCalldata(tr, p, degree);
            uint256 msgAt = p;
            p += 16 * degree;
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p), bits);
            p += 8;
            rs[i] = r;
            st.v[Staged.CLAIM] = _round(msgAt, degree, st.v[Staged.CLAIM], r);
        }
        return (rs, p);
    }

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

    /// Checks the supplied counts against those an earlier stage saw, remembering them if none did.
    function _countsHash(State memory st, uint256 at) private pure {
        uint256 a = uint256(Staged.hashAt(at, 16 * P_AT));
        uint256 b = uint256(Staged.hashAt(at + 16 * P_AT, 16 * (COUNTS - P_AT)));
        if (st.v[Staged.COUNTS_HASH_A] == 0 && st.v[Staged.COUNTS_HASH_P] == 0) {
            st.v[Staged.COUNTS_HASH_A] = a;
            st.v[Staged.COUNTS_HASH_P] = b;
        } else if (st.v[Staged.COUNTS_HASH_A] != a || st.v[Staged.COUNTS_HASH_P] != b) {
            revert Counts();
        }
    }

    /// Items `9c` to `9c + 8`: claim `c`'s side and word-chunk dots, then its prefix dot in eight
    /// ranges of bit positions.
    function _dots(State memory st, uint256 upto, bytes calldata data) private pure returns (uint256[] memory) {
        uint256 cursor = st.v[Staged.CURSOR];
        if (upto <= cursor || upto > st.v[Staged.ITEMS] || data.length != 16 * COUNTS) revert Shape();
        uint256 at = Staged.offset(data);
        _countsHash(st, at);
        uint256[] memory suffix;
        for (uint256 item = cursor; item < upto; ++item) {
            uint256 c = item / DOT_ITEMS;
            uint256 j = item % DOT_ITEMS;
            if (j == 0) {
                st.a[Staged.ACCS][c] = _chunkTerm(st, c, at);
                continue;
            }
            if (suffix.length == 0) {
                suffix = _suffix(at + 16 * P_AT);
            }
            st.v[Staged.PREFIX_ACC] ^= _prefixDot(
                suffix, _slice(st.a[Staged.SKIPS], 64 * c, 64), _zp(st, c), 8 * (j - 1), 8 * j
            );
            if (j == DOT_ITEMS - 1) {
                st.v[Staged.EXPECTED] ^= GF2.mul(st.a[Staged.ACCS][c], st.v[Staged.PREFIX_ACC]);
                st.v[Staged.PREFIX_ACC] = 0;
            }
        }
        st.v[Staged.CURSOR] = upto;
        if (upto < st.v[Staged.ITEMS]) {
            return _countStreams(st);
        }
        if (st.v[Staged.EXPECTED] != st.v[Staged.CLAIM]) revert MainSumcheck();
        Staged.enter(st, Staged.M_COUNTS, 1);
        return Staged.want2(_countStreams(st), Staged.sequential(st.v[Staged.POS]));
    }

    function _zp(State memory st, uint256 c) private pure returns (uint256[] memory) {
        return _slice(st.a[Staged.PACKED], c * CLAIM_WORDS + 48, 64);
    }

    function _chunkTerm(State memory st, uint256 c, uint256 at) private pure returns (uint256 term) {
        uint256[] memory claims = st.a[Staged.PACKED];
        uint256 b = c * CLAIM_WORDS;
        uint256 side = GF2.mul(claims[b], Calldata.f128(at)) ^ Calldata.f128(at + 16);
        term = GF2.mul(st.a[Staged.WEIGHTS][c], side);
        term = GF2.mul(term, _chunkDots(at, _slice(claims, b + 4, LOG_LEN), 2));
        term = GF2.mul(term, _chunkDots(at, _slice(claims, b + 26, LOG_LEN), 578));
    }

    function _chunkDots(uint256 countsAt, uint256[] memory point, uint256 from) private pure returns (uint256 acc) {
        acc = 1;
        uint256 at = countsAt + 16 * from;
        uint256[3] memory widths = [uint256(8), 8, 6];
        uint256 start_;
        for (uint256 k = 0; k < 3; ++k) {
            acc = GF2.mul(acc, _dotAt(GF2.eqTable(_slice(point, start_, widths[k])), at));
            start_ += widths[k];
            at += 16 << widths[k];
        }
    }

    function _dotAt(uint256[] memory t, uint256 at) private pure returns (uint256 acc) {
        uint256 len = t.length;
        for (uint256 i = 0; i < len; ++i) {
            acc ^= GF2.mul(t[i], Calldata.f128(at + 16 * i));
        }
    }

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

    function _prefixDot(uint256[] memory s, uint256[] memory skip, uint256[] memory z, uint256 from, uint256 to)
        private
        pure
        returns (uint256 acc)
    {
        for (uint256 t = from; t < to; ++t) {
            uint256 inner;
            for (uint256 v = 0; v < 64; ++v) {
                uint256 m = s[((v + 64 - t) & 63) * 64 + t] ^ s[(64 + v) * 64 + t];
                inner ^= GF2.mul(z[v], m);
            }
            acc ^= GF2.mul(skip[t], inner);
        }
    }

    /// Absorbs the counts, samples the count check's batching and points, and sums every lookup
    /// but the prefix table's.
    function _counts(State memory st, bytes calldata data) private pure returns (uint256[] memory) {
        if (data.length < 16 * COUNTS + 8) revert Shape();
        uint256 at = Staged.offset(data);
        _countsHash(st, at);
        _countPoints(st, at);
        uint256[8] memory widths = [uint256(1), 8, 8, 6, 8, 8, 6, 14];
        uint256 claim;
        uint256 from = at;
        for (uint256 l = 0; l < 7; ++l) {
            uint256 dot = _dotAt(GF2.eqTable(st.a[Staged.POINTS + l]), from);
            claim ^= GF2.mul(st.a[Staged.M_GAMMAS][l], dot);
            from += 16 << widths[l];
        }
        st.v[Staged.CLAIM] = claim;
        st.v[Staged.PREFIX_ACC] = 0;
        st.v[Staged.ROWS_SEEN] = 0;
        st.v[Staged.ROWS_CHAIN] = _chain(0, at + 16 * P_AT, 128);
        st.v[Staged.POS] += 8;
        st.v[Staged.READ] = st.v[Staged.POS];
        Staged.enter(st, Staged.M_PREFIX, 128);
        return Staged.want1(Staged.PROOF, st.v[Staged.COUNTS_AT] + 16 * P_AT, 16 * P_COLS, 0);
    }

    /// Absorbs the counts at `at` and samples the count check's batching and points.
    function _countPoints(State memory st, uint256 at) private pure {
        uint256 tr = Staged.restoreSized(st.tr, 16 * COUNTS + 4096);
        Transcript.observeSliceFromCalldata(tr, at, COUNTS);
        uint256 gamma = Transcript.powSample(tr, Calldata.nonce(at + 16 * COUNTS), 5);
        uint256[8] memory widths = [uint256(1), 8, 8, 6, 8, 8, 6, 14];
        uint256[] memory gammas = new uint256[](8);
        uint256 g = 1;
        for (uint256 l = 0; l < 8; ++l) {
            st.a[Staged.POINTS + l] = Transcript.sampleVec(tr, widths[l]);
            gammas[l] = g;
            g = GF2.mul(g, gamma);
        }
        st.a[Staged.M_GAMMAS] = gammas;
        st.tr = Staged.keep(tr);
    }

    /// Rows of the prefix table's weighted count, which must match the counts seen before.
    function _prefix(State memory st, uint256 upto, bytes calldata data) private pure returns (uint256[] memory) {
        uint256 cursor = st.v[Staged.CURSOR];
        if (upto <= cursor || upto > 128 || data.length != 16 * P_COLS * (upto - cursor)) revert Shape();
        uint256[] memory point = st.a[Staged.POINTS + 7];
        uint256[] memory eqLo = GF2.eqTable(_slice(point, 0, 7));
        uint256[] memory eqHi = GF2.eqTable(_slice(point, 7, 7));
        uint256 at = Staged.offset(data);
        uint256 acc = st.v[Staged.PREFIX_ACC];
        for (uint256 u = cursor; u < upto; ++u) {
            uint256 row;
            uint256 base = at + 16 * (u - cursor) * P_COLS;
            for (uint256 j = 0; j < P_COLS; ++j) {
                row ^= GF2.mul(eqLo[j], Calldata.f128(base + 16 * j));
            }
            acc ^= GF2.mul(eqHi[u], row);
        }
        st.v[Staged.PREFIX_ACC] = acc;
        st.v[Staged.ROWS_SEEN] = _chain(st.v[Staged.ROWS_SEEN], at, upto - cursor);
        st.v[Staged.CURSOR] = upto;
        if (upto < 128) {
            return Staged.want1(Staged.PROOF, st.v[Staged.COUNTS_AT] + 16 * P_AT, 16 * P_COLS, 0);
        }
        if (st.v[Staged.ROWS_SEEN] != st.v[Staged.ROWS_CHAIN]) revert Counts();
        st.v[Staged.CLAIM] ^= GF2.mul(st.a[Staged.M_GAMMAS][7], acc);
        Staged.enter(st, Staged.M_BITS, 1);
        return Staged.sequential(st.v[Staged.POS]);
    }

    /// `keccak(chain ‖ row)` folded over the `count` rows of the prefix table at `at`.
    function _chain(uint256 chain, uint256 at, uint256 count) private pure returns (uint256) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let len := mul(16, P_COLS)
            for { let u := 0 } lt(u, count) { u := add(u, 1) } {
                mstore(ptr, chain)
                calldatacopy(add(ptr, 0x20), add(at, mul(u, len)), len)
                chain := keccak256(ptr, add(len, 0x20))
            }
        }
        return chain;
    }

    /// The count sumcheck, the address bits' check and the opened claim.
    function _bits(State memory st, uint256 p) private pure {
        uint256 p0 = p;
        uint256 tr = Staged.restore(st.tr);
        uint256[] memory sigma;
        (sigma, p) = _sumcheck(st, tr, p, COUNT_DEGREE, 4);
        uint256 bitsAt = p;
        p += 16 * ADDRESS_BITS;
        uint256[] memory rho = st.a[Staged.RHO];
        uint256 eq = 1;
        for (uint256 i = 0; i < LOG_LEN; ++i) {
            eq = GF2.mul(eq, 1 ^ rho[i] ^ sigma[i]);
        }
        if (GF2.mul(eq, _bitsSum(st, bitsAt)) != st.v[Staged.CLAIM]) revert CountSumcheck();
        Transcript.observeSliceFromCalldata(tr, bitsAt, ADDRESS_BITS);
        uint256 zeta = Transcript.powSample(tr, Calldata.nonce(p), 6);
        p += 8;
        uint256[] memory w = Piop.lagrange(Constants.PHI8, zeta);
        uint256 value;
        for (uint256 i = 0; i < ADDRESS_BITS; ++i) {
            value ^= GF2.mul(w[i], Calldata.f128(bitsAt + 16 * i));
        }
        uint256[] memory zs = new uint256[](1);
        uint256[] memory values = new uint256[](1);
        zs[0] = zeta;
        values[0] = value;
        st.a[Staged.CL_Z] = zs;
        st.a[Staged.CL_VALUE] = values;
        st.a[Staged.CL_X] = sigma;
        st.v[Staged.NCLAIMS] = 1;
        st.v[Staged.POS] += p - p0;
        st.v[Staged.READ] = st.v[Staged.POS];
        st.tr = Staged.keep(tr);
        for (uint256 l = 0; l < 8; ++l) {
            st.a[Staged.POINTS + l] = new uint256[](0);
        }
        st.a[Staged.SKIPS] = new uint256[](0);
        st.a[Staged.PACKED] = new uint256[](0);
        Staged.enter(st, Staged.SWITCH, 1);
    }

    function _bitsSum(State memory st, uint256 bitsAt) private pure returns (uint256 sum) {
        uint256[8] memory offsets = [uint256(0), 1, 9, 17, 23, 31, 39, 45];
        for (uint256 l = 0; l < 8; ++l) {
            uint256 prod = st.a[Staged.M_GAMMAS][l];
            uint256[] memory point = st.a[Staged.POINTS + l];
            for (uint256 i = 0; i < point.length; ++i) {
                prod = GF2.mul(prod, 1 ^ point[i] ^ Calldata.f128(bitsAt + 16 * (offsets[l] + i)));
            }
            sum ^= prod;
        }
    }

    function _check(State memory st) private pure returns (bytes memory, uint256[] memory) {
        if (st.v[Staged.GOT] != st.v[Staged.CLAIM]) revert Final();
        return (abi.encodePacked(bytes32(Staged.MATRIX_DONE), bytes32(st.v[Staged.DIGEST])), new uint256[](0));
    }
}
