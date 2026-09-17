// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Transcript} from "../Transcript.sol";

/// The state a staged verification carries between transactions: named scalars, named arrays
/// and the transcript.
struct State {
    uint256[] v;
    uint256[][] a;
    bytes tr;
}

/// One contract running some of the stages of a staged verification.
interface IStage {
    /// Runs the current stage of `state` over its items up to `upto`, reading `data`, and returns
    /// the next state with what its stage reads: `[source, base, unit, length]` per stream,
    /// `unit` bytes per item from `base`, or `length` bytes from `base` in every call, or, with
    /// both zero, the bytes from `base` that the stage consumes.
    function run(bytes calldata state, uint256 upto, bytes calldata data)
        external
        view
        returns (bytes memory next, uint256[] memory want);
}

/// Stage numbers, state layout and helpers of the staged verifiers.
library Staged {
    // Stages. The session sends stages below 20 to the lift stages, 20–39 to the opening stages,
    // 40–49 to the residual stages, 50–69 to the matrix stages and 70–79 to the structured stages.
    uint256 internal constant WORDS = 1;
    uint256 internal constant HEAD = 2;
    uint256 internal constant IO = 3;
    uint256 internal constant CHECK = 4;
    uint256 internal constant GATE = 5;
    uint256 internal constant LIFT_DONE = 19;
    uint256 internal constant SWITCH = 20;
    uint256 internal constant OPEN = 21;
    uint256 internal constant LEVEL = 22;
    uint256 internal constant FINISH = 23;
    uint256 internal constant OOD = 24;
    uint256 internal constant RS = 40;
    uint256 internal constant CONS = 41;
    uint256 internal constant M_START = 50;
    uint256 internal constant M_MAIN = 51;
    uint256 internal constant M_DOTS = 52;
    uint256 internal constant M_COUNTS = 53;
    uint256 internal constant M_PREFIX = 54;
    uint256 internal constant M_BITS = 55;
    uint256 internal constant M_CHECK = 56;
    uint256 internal constant MATRIX_DONE = 69;
    uint256 internal constant STRUCT = 70;

    // Sources of stream bytes.
    uint256 internal constant PROOF = 0;
    uint256 internal constant OUTPUT = 1;
    uint256 internal constant BINDING = 2;
    /// A request's closing entry: where the last sequential read ended, the cursor and the item
    /// count.
    uint256 internal constant MARK = 99;

    // Scalars.
    uint256 internal constant STAGE = 0;
    uint256 internal constant CURSOR = 1;
    uint256 internal constant ITEMS = 2;
    uint256 internal constant KIND = 3;
    uint256 internal constant POS = 4;
    uint256 internal constant N = 5;
    uint256 internal constant CHUNK = 6;
    uint256 internal constant NIO = 7;
    uint256 internal constant CHUNK_I = 8;
    uint256 internal constant NCHUNKS = 9;
    uint256 internal constant LIVE = 10;
    uint256 internal constant NU = 11;
    uint256 internal constant M = 12;
    uint256 internal constant SLIM = 13;
    uint256 internal constant DIGEST = 14;
    uint256 internal constant WORDS_AT = 15;
    uint256 internal constant UNOPENED_AT = 16;
    uint256 internal constant STATEMENT = 17;
    uint256 internal constant CLAIM = 18;
    uint256 internal constant QC = 19;
    uint256 internal constant QB = 20;
    uint256 internal constant QA = 21;
    uint256 internal constant LOG_N = 22;
    uint256 internal constant SPLIT_DIM = 23;
    uint256 internal constant PREV_LANES = 24;
    uint256 internal constant PREV_COLS = 25;
    uint256 internal constant PREV_RATE = 26;
    uint256 internal constant TARGET = 27;
    uint256 internal constant LEVEL_I = 28;
    uint256 internal constant NOOD = 29;
    uint256 internal constant NCONS = 30;
    uint256 internal constant EXT = 31;
    uint256 internal constant WIDTH = 32;
    uint256 internal constant PATH_LEN = 33;
    uint256 internal constant ENFORCED = 34;
    uint256 internal constant GOT = 35;
    uint256 internal constant FINAL = 36;
    uint256 internal constant ROWS_AT = 37;
    uint256 internal constant PATHS_AT = 38;
    uint256 internal constant RS_ACC = 39;
    uint256 internal constant RS_PART = 40;
    uint256 internal constant IO_VALUE = 41;
    uint256 internal constant IO_LAST = 42;
    uint256 internal constant NCLAIMS = 43;
    uint256 internal constant STEPS = 44;
    uint256 internal constant INITIAL_K = 45;
    uint256 internal constant COUNTS_AT = 46;
    uint256 internal constant COUNTS_HASH_A = 47;
    uint256 internal constant COUNTS_HASH_P = 48;
    uint256 internal constant EXPECTED = 49;
    uint256 internal constant GAMMA7 = 50;
    uint256 internal constant PREFIX_ACC = 51;
    uint256 internal constant OUTPUT_LEN = 52;
    uint256 internal constant BINDING_LEN = 53;
    uint256 internal constant COUNTS = 54;
    uint256 internal constant CHUNK_END = 55;
    uint256 internal constant FIRST_KECCAK = 56;
    uint256 internal constant KECCAK_SUBS = 57;
    uint256 internal constant ROWS_CHAIN = 58;
    uint256 internal constant ROWS_SEEN = 59;
    uint256 internal constant READ = 60;
    uint256 internal constant SCALARS = 61;

    // Arrays.
    uint256 internal constant WORD_HASHES = 0;
    uint256 internal constant PACKED = 1;
    uint256 internal constant MC = 2;
    uint256 internal constant CL_Z = 3;
    uint256 internal constant CL_VALUE = 4;
    uint256 internal constant CL_X = 5;
    uint256 internal constant RDP = 8;
    uint256 internal constant GAMMAS = 9;
    uint256 internal constant CFG_RATES = 10;
    uint256 internal constant CFG_KS = 11;
    uint256 internal constant CFG_QUERIES = 12;
    uint256 internal constant CFG_GRINDING = 13;
    uint256 internal constant CFG_CLAIM_BITS = 14;
    uint256 internal constant CFG_CONS_BITS = 15;
    uint256 internal constant CFG_OOD = 16;
    uint256 internal constant CFG_BLOCK_LENS = 17;
    uint256 internal constant CFG_DEPTHS = 18;
    uint256 internal constant CAP = 19;
    uint256 internal constant NEXT_CAP = 20;
    uint256 internal constant INITIAL = 21;
    uint256 internal constant LEVELS = 22;
    uint256 internal constant OOD_BETA = 30;
    uint256 internal constant OOD_SPLIT = 31;
    uint256 internal constant OOD_POINT = 32;
    uint256 internal constant CONS_BETA = 48;
    uint256 internal constant CONS_COLS = 49;
    uint256 internal constant CONS_START = 50;
    uint256 internal constant CONS_Q = 51;
    uint256 internal constant CONS_ALPHA = 60;
    uint256 internal constant RW = 69;
    uint256 internal constant LANES = 70;
    uint256 internal constant COLS = 71;
    uint256 internal constant MU = 72;
    uint256 internal constant WORK = 73;
    uint256 internal constant RS_NG = 74;
    uint256 internal constant KERNEL = 75;
    uint256 internal constant PAIRS = 76;
    uint256 internal constant ACCS = 77;
    uint256 internal constant VALUES = 78;
    uint256 internal constant WEIGHTS = 79;
    uint256 internal constant RHO = 80;
    uint256 internal constant SIGMA = 81;
    uint256 internal constant M_GAMMAS = 82;
    uint256 internal constant POINTS = 83;
    uint256 internal constant SKIPS = 91;
    uint256 internal constant ARRAYS = 92;

    uint256 internal constant MAX_OODS = 16;
    uint256 internal constant MAX_LEVELS = 8;
    uint256 internal constant TRANSCRIPT_CAPACITY = 1 << 17;

    error StageMismatch();

    /// A fresh state of `kind`.
    function fresh(uint256 kind) internal pure returns (State memory st) {
        st.v = new uint256[](SCALARS);
        st.a = new uint256[][](ARRAYS);
        st.v[KIND] = kind;
    }

    /// The state encoded in `state`, which must be at `stage` range `[lo, hi]`.
    function load(bytes calldata state, uint256 lo, uint256 hi) internal pure returns (State memory st) {
        uint256 stage = uint256(bytes32(state[:32]));
        if (stage < lo || stage > hi) revert StageMismatch();
        st = abi.decode(state[32:], (State));
    }

    /// The encoding of `st`, led by its stage.
    function save(State memory st) internal pure returns (bytes memory) {
        return bytes.concat(bytes32(st.v[STAGE]), abi.encode(st));
    }

    /// Moves `st` to `stage` over `items` items.
    function enter(State memory st, uint256 stage, uint256 items) internal pure {
        st.v[STAGE] = stage;
        st.v[CURSOR] = 0;
        st.v[ITEMS] = items;
    }

    /// A stream request: `unit` bytes per item, or `length` bytes per call, from `base`.
    function want1(uint256 source, uint256 base, uint256 unit, uint256 length) internal pure returns (uint256[] memory w) {
        w = new uint256[](4);
        w[0] = source;
        w[1] = base;
        w[2] = unit;
        w[3] = length;
    }

    /// Two stream requests.
    function want2(uint256[] memory x, uint256[] memory y) internal pure returns (uint256[] memory w) {
        w = new uint256[](x.length + y.length);
        for (uint256 i = 0; i < x.length; ++i) {
            w[i] = x[i];
        }
        for (uint256 i = 0; i < y.length; ++i) {
            w[x.length + i] = y[i];
        }
    }

    /// `streams` closed by the state's proof position, cursor and item count.
    function request(State memory st, uint256[] memory streams) internal pure returns (uint256[] memory w) {
        w = new uint256[](streams.length + 4);
        for (uint256 i = 0; i < streams.length; ++i) {
            w[i] = streams[i];
        }
        uint256 n = streams.length;
        w[n] = MARK;
        w[n + 1] = st.v[READ];
        w[n + 2] = st.v[CURSOR];
        w[n + 3] = st.v[ITEMS];
    }

    /// Appends `w`'s words, `32·w.length` bytes, to the pending bytes of transcript `tr`.
    function absorbWords(uint256 tr, uint256[] memory w) internal pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            let len := shl(5, mload(w))
            mcopy(add(add(tr, 0x40), l), add(w, 0x20), len)
            mstore(add(tr, 0x20), add(l, len))
        }
    }

    /// The bytes a sequential stage reads from the proof at `pos`.
    function sequential(uint256 pos) internal pure returns (uint256[] memory) {
        return want1(PROOF, pos, 0, 0);
    }

    /// The calldata offset of `b`.
    function offset(bytes calldata b) internal pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }

    /// A live transcript restored from `saved`: the chaining value, then the pending bytes.
    function restore(bytes memory saved) internal pure returns (uint256) {
        return restoreSized(saved, TRANSCRIPT_CAPACITY);
    }

    /// `restore` with room for `capacity` pending bytes.
    function restoreSized(bytes memory saved, uint256 capacity) internal pure returns (uint256 tr) {
        assembly ("memory-safe") {
            tr := mload(0x40)
            mstore(0x40, add(tr, add(capacity, 128)))
            let len := mload(saved)
            mstore(tr, mload(add(saved, 0x20)))
            mstore(add(tr, 0x20), sub(len, 32))
            mcopy(add(tr, 0x40), add(saved, 0x40), sub(len, 32))
        }
    }

    /// The transcript `tr` as `restore` reads it.
    function keep(uint256 tr) internal pure returns (bytes memory saved) {
        assembly ("memory-safe") {
            let len := mload(add(tr, 0x20))
            saved := mload(0x40)
            mstore(saved, add(len, 32))
            mstore(add(saved, 0x20), mload(tr))
            mcopy(add(saved, 0x40), add(tr, 0x40), len)
            mstore(0x40, add(add(saved, 0x40), and(add(len, 31), not(31))))
        }
    }

    /// A fresh transcript under the domain `domain`, saved.
    function transcript(bytes memory domain) internal pure returns (bytes memory) {
        return keep(Transcript.createFromMemory(domain));
    }

    /// A copy of `n` calldata words at `at`.
    function words(uint256 at, uint256 n) internal pure returns (uint256[] memory w) {
        w = new uint256[](n);
        assembly ("memory-safe") {
            calldatacopy(add(w, 0x20), at, shl(5, n))
        }
    }

    /// Keccak-256 of `len` calldata bytes at `at`.
    function hashAt(uint256 at, uint256 len) internal pure returns (bytes32 h) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, at, len)
            h := keccak256(ptr, len)
        }
    }
}
