// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Constants} from "../Constants.sol";
import {FiatShamir, OutputShape} from "../FiatShamir.sol";
import {GF2} from "../GF2.sol";
import {MatrixClaim, Piop, ZerocheckOut, Claim} from "../Piop.sol";
import {Transcript} from "../Transcript.sol";
import {Config} from "./Config.sol";
import {IStage, Staged, State} from "./Staged.sol";

/// Where a lift's published words sit, and the entry into a chunk's first stage.
library LiftLayout {
    /// The header, the published words and the unopened digests.
    function region(State memory st) internal pure returns (uint256[] memory) {
        return Staged.want1(Staged.PROOF, 0, 0, st.v[Staged.UNOPENED_AT] + 32 * st.v[Staged.N]);
    }

    /// Where chunk `i`'s published words sit in the proof, and their length.
    function chunkWords(State memory st, uint256 i) internal pure returns (uint256 from, uint256 len) {
        uint256 n = st.v[Staged.N];
        uint256 chunk = st.v[Staged.CHUNK];
        uint256 live = n - i * chunk < chunk ? n - i * chunk : chunk;
        from = st.v[Staged.WORDS_AT] + 16 * st.v[Staged.NIO] * i * chunk;
        len = 16 * st.v[Staged.NIO] * live;
    }

    function enterHead(State memory st) internal pure returns (uint256[] memory) {
        uint256 i = st.v[Staged.CHUNK_I];
        uint256 n = st.v[Staged.N];
        uint256 chunk = st.v[Staged.CHUNK];
        uint256 live = n - i * chunk < chunk ? n - i * chunk : chunk;
        uint256 nu = 3;
        while ((1 << nu) < live) {
            ++nu;
        }
        st.v[Staged.LIVE] = live;
        st.v[Staged.NU] = nu;
        st.v[Staged.M] = Piop.K_LOG + nu;
        Staged.enter(st, Staged.HEAD, 1);
        (uint256 from, uint256 len) = chunkWords(st, i);
        return Staged.want2(Staged.want1(Staged.PROOF, from, 0, len), Staged.sequential(st.v[Staged.POS]));
    }

    function rowStreams(State memory st) internal pure returns (uint256[] memory) {
        (uint256 from,) = chunkWords(st, st.v[Staged.CHUNK_I]);
        return Staged.want1(Staged.PROOF, from, 16 * st.v[Staged.NIO], 0);
    }

}

/// The lift's first stages, for one pinned statement circuit (as `FlockLift`): the published
/// words, and each chunk's PIOP up to its opening.
contract LiftStages is IStage {
    bytes internal constant LIFT_VERSION = "pofseed-flock-lift-v1";
    uint256 internal constant MAX_CHUNK = 128;

    /// The structural fingerprint of the statement circuit, which fixes its chain code and index.
    bytes32 public immutable fingerprint;
    /// The parent chain code.
    bytes32 public immutable chainCode;
    /// The child index.
    uint32 public immutable index;
    /// The fewest responses a lift may carry.
    uint256 public immutable minResponses;
    /// The expected output's word counts: 8-bit words, then 32-bit words shifted by 16, then
    /// 64-bit words shifted by 32.
    uint256 public immutable counts;
    /// Whether chunks are opened under Ligerito's `Slim` profile rather than `Fast`.
    bool public immutable slim;

    error Shape();
    error AssertionWord();
    error TooFewResponses();
    error Words();
    error Final();

    constructor(bytes32 fingerprint_, bytes32 chainCode_, uint32 index_, uint256 minResponses_, uint256 counts_, bool slim_) {
        counts = counts_;
        fingerprint = fingerprint_;
        chainCode = chainCode_;
        index = index_;
        minResponses = minResponses_;
        slim = slim_;
    }

    /// The first state of a lift verification of `n` responses in chunks of `chunk`, against
    /// the expected output `output` (word counts packed as in `FlockLift.verify`) under `binding`.
    function start(bytes calldata output, uint256 counts_, bytes calldata binding, uint256 n, uint256 chunk)
        external
        view
        returns (bytes memory, uint256[] memory)
    {
        if (counts_ != counts) revert Shape();
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        if (s.counts[0] == 0 || output[s.at[0] + s.counts[0] - 1] != 0x01) revert AssertionWord();
        if (n < minResponses) revert TooFewResponses();
        if (chunk == 0 || chunk > MAX_CHUNK) revert Shape();
        State memory st = Staged.fresh(1);
        st.v[Staged.N] = n;
        st.v[Staged.CHUNK] = chunk;
        st.v[Staged.NIO] = 5 + 2 * ((8 * s.payload + 127) / 128);
        st.v[Staged.NCHUNKS] = (n + chunk - 1) / chunk;
        st.v[Staged.SLIM] = slim ? 1 : 0;
        st.v[Staged.WORDS_AT] = 8;
        st.v[Staged.UNOPENED_AT] = 8 + 16 * st.v[Staged.NIO] * n;
        st.v[Staged.DIGEST] = uint256(_statementDigest(output, binding, n, chunk));
        st.v[Staged.STATEMENT] = uint256(keccak256(abi.encodePacked(output, binding, counts)));
        st.v[Staged.OUTPUT_LEN] = output.length;
        st.v[Staged.BINDING_LEN] = binding.length;
        st.v[Staged.COUNTS] = counts;
        Staged.enter(st, Staged.WORDS, 1);
        return (Staged.save(st), Staged.request(st, LiftLayout.region(st)));
    }

    function run(bytes calldata state, uint256, bytes calldata data)
        external
        view
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.WORDS, Staged.HEAD);
        uint256[] memory streams;
        if (st.v[Staged.STAGE] == Staged.WORDS) {
            streams = _words(st, data);
        } else {
            _head(st, data);
            streams = LiftLayout.rowStreams(st);
        }
        return (Staged.save(st), Staged.request(st, streams));
    }

    function _words(State memory st, bytes calldata data) private pure returns (uint256[] memory) {
        uint256 len = st.v[Staged.UNOPENED_AT] + 32 * st.v[Staged.N];
        if (data.length != len) revert Words();
        uint256 at = Staged.offset(data);
        if (Calldata.u32(at) != st.v[Staged.CHUNK] || Calldata.u32(at + 4) != st.v[Staged.N]) revert Shape();
        uint256 chunks = st.v[Staged.NCHUNKS];
        uint256[] memory hashes = new uint256[](chunks + 1);
        for (uint256 i = 0; i < chunks; ++i) {
            (uint256 from, uint256 wlen) = LiftLayout.chunkWords(st, i);
            hashes[i] = uint256(Staged.hashAt(at + from, wlen));
        }
        hashes[chunks] = uint256(Staged.hashAt(at, len));
        st.a[Staged.WORD_HASHES] = hashes;
        st.v[Staged.POS] = len;
        st.v[Staged.CHUNK_I] = 0;
        return LiftLayout.enterHead(st);
    }

    function _head(State memory st, bytes calldata data) private view {
        uint256 i = st.v[Staged.CHUNK_I];
        (, uint256 wlen) = LiftLayout.chunkWords(st, i);
        uint256 wordsAt = Staged.offset(data);
        if (uint256(Staged.hashAt(wordsAt, wlen)) != st.a[Staged.WORD_HASHES][i]) revert Words();
        Config.fill(st, st.v[Staged.M], slim);
        (uint256 tr, uint256 p) = _headTranscript(st, wordsAt, wordsAt + wlen);
        uint256 end = _headPiop(st, tr, p);
        st.v[Staged.POS] += end - wordsAt - wlen;
        st.v[Staged.READ] = st.v[Staged.POS];
        st.tr = Staged.keep(tr);
        Staged.enter(st, Staged.IO, st.v[Staged.LIVE]);
    }

    /// The chunk's transcript up to its PIOP, and where the PIOP's messages start.
    function _headTranscript(State memory st, uint256 wordsAt, uint256 p) private pure returns (uint256 tr, uint256) {
        uint256 m = st.v[Staged.M];
        st.v[Staged.CHUNK_END] = st.v[Staged.POS] + 4 + Calldata.u32(p);
        uint256 capLen = 1 << Config.capDepth(st, 0);
        uint256 capAt = p + 4;
        st.a[Staged.CAP] = Staged.words(capAt, capLen);
        bytes memory domain = abi.encodePacked(
            LIFT_VERSION, bytes32(st.v[Staged.DIGEST]), bytes8(uint64(FiatShamir.uint64le(st.v[Staged.CHUNK_I])))
        );
        tr = Transcript.createFromMemory(domain);
        Piop.observeWords(tr, wordsAt, st.v[Staged.LIVE], st.v[Staged.NIO], st.v[Staged.NU]);
        Transcript.label(tr, Constants.L_R1CS_0, Constants.L_R1CS_1, Constants.L_R1CS_LEN);
        Transcript.header(tr, 5, 0, 32);
        Transcript.raw(tr, _statementDigestOf(m));
        Transcript.header(tr, 5, 0, 32 * capLen);
        Transcript.bytesFromCalldata(tr, capAt, 32 * capLen);
        return (tr, capAt + 32 * capLen);
    }

    /// Runs the zerocheck and the lincheck from `p` and returns where they end.
    function _headPiop(State memory st, uint256 tr, uint256 p) private pure returns (uint256) {
        ZerocheckOut memory zc;
        (p, zc) = Piop.zerocheck(tr, Constants.PHI8, p, st.v[Staged.M]);
        MatrixClaim memory mc;
        Claim memory ab;
        (p, mc, ab) = Piop.lincheck(tr, Constants.PHI8, p, zc);
        st.a[Staged.MC] = _pack(mc);
        _ioPoint(st, tr, zc, ab);
        return p;
    }

    /// Samples the published-word claim's point and records the chunk's three opening claims, the
    /// published-word claim's value still to come.
    function _ioPoint(State memory st, uint256 tr, ZerocheckOut memory zc, Claim memory ab) private pure {
        uint256 nu = st.v[Staged.NU];
        uint256 z = Transcript.sample(tr);
        uint256[] memory io = new uint256[](6 + nu);
        io[0] = z;
        io[1] = Transcript.sample(tr);
        for (uint256 k = 0; k < 4; ++k) {
            io[2 + k] = Transcript.sample(tr);
        }
        for (uint256 k = 0; k < nu; ++k) {
            io[6 + k] = Transcript.sample(tr);
        }
        uint256[] memory x = new uint256[](Piop.K_LOG - Piop.K_SKIP + nu);
        x[0] = io[1];
        for (uint256 k = 0; k < 4; ++k) {
            x[1 + k] = io[2 + k];
        }
        for (uint256 bit = 11; bit < Piop.K_LOG; ++bit) {
            x[bit - 6] = (Piop.IO_BASE_BITS >> bit) & 1;
        }
        for (uint256 k = 0; k < nu; ++k) {
            x[Piop.K_LOG - Piop.K_SKIP + k] = io[6 + k];
        }
        st.a[Staged.ACCS] = io;
        uint256[] memory zs = new uint256[](3);
        uint256[] memory values = new uint256[](3);
        zs[0] = ab.z;
        zs[1] = zc.z;
        zs[2] = z;
        values[0] = ab.value;
        values[1] = zc.c;
        st.a[Staged.CL_Z] = zs;
        st.a[Staged.CL_VALUE] = values;
        st.a[Staged.CL_X] = ab.x;
        st.a[Staged.CL_X + 1] = zc.rRest;
        st.a[Staged.CL_X + 2] = x;
        st.v[Staged.NCLAIMS] = 3;
        st.v[Staged.IO_VALUE] = 0;
        st.v[Staged.IO_LAST] = 0;
    }

    /// The matrix claim flattened as `FlockLift` returns it.
    function _pack(MatrixClaim memory c) private pure returns (uint256[] memory out) {
        out = new uint256[](112);
        out[0] = c.alpha;
        out[1] = c.beta;
        out[2] = c.z;
        out[3] = c.running;
        for (uint256 k = 0; k < 22; ++k) {
            out[4 + k] = c.xInnerRest[k];
            out[26 + k] = c.rInnerRest[k];
        }
        for (uint256 k = 0; k < 64; ++k) {
            out[48 + k] = c.zPartial[k];
        }
    }

    function _framed(bytes memory tag, bytes memory body) private pure returns (bytes memory) {
        return abi.encodePacked(tag, bytes8(uint64(FiatShamir.uint64le(body.length))), body);
    }

    function _statementDigest(bytes calldata output, bytes calldata binding, uint256 n, uint256 chunk)
        private
        view
        returns (bytes32)
    {
        bytes memory idx = abi.encodePacked(bytes4(uint32(FiatShamir.uint64le(index) >> 32)));
        bytes memory responses = abi.encodePacked(bytes8(uint64(FiatShamir.uint64le(n))));
        bytes memory chunkBytes = abi.encodePacked(bytes4(uint32(FiatShamir.uint64le(chunk) >> 32)));
        bytes memory head = abi.encodePacked(
            _framed(LIFT_VERSION, abi.encodePacked(fingerprint)),
            _framed("chain-code", abi.encodePacked(chainCode)),
            _framed("index", idx)
        );
        bytes memory tail = abi.encodePacked(
            _framed("binding", binding), _framed("responses", responses), _framed("chunk", chunkBytes)
        );
        return keccak256(bytes.concat(head, _framed("expected-output", output), tail));
    }

    function _statementDigestOf(uint256 m) private pure returns (bytes32) {
        if (m == 31) return Constants.STATEMENT_DIGEST_31;
        if (m == 32) return Constants.STATEMENT_DIGEST_32;
        if (m == 33) return Constants.STATEMENT_DIGEST_33;
        if (m == 34) return Constants.STATEMENT_DIGEST_34;
        if (m == 35) return Constants.STATEMENT_DIGEST_35;
        revert Shape();
    }
}
