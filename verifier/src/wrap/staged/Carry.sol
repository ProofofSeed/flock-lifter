// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Whir, WhirState} from "../Whir.sol";
import {W} from "../W.sol";

/// What a staged verification of a wrapped lift carries between transactions: the stage to run
/// next, the statement's digest, named scalars, named arrays and named byte strings.
struct Carry {
    uint256 stage;
    bytes32 digest;
    uint256[] v;
    uint256[][] a;
    bytes[] b;
}

/// One contract running one stage of the staged verification.
interface IWrapStage {
    /// Runs the stage `c` is at, reading `data` from the lift's encoding at the state's cursor, and
    /// returns the encoded next state.
    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory next);
}

/// The contract starting a staged verification.
interface IWrapStart {
    /// Runs the first stage on the expected output, its word counts, the binding and the start of
    /// the lift's encoding, and returns the encoded next state.
    function start(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata data)
        external
        view
        returns (bytes memory next);
}

/// The carried state's layout, and its conversions to and from the verifier's working memory.
library Stage {
    uint256 internal constant DONE = 8;

    // Scalars.
    uint256 internal constant CURSOR = 0;
    uint256 internal constant TR = 1;
    uint256 internal constant CHILD = 2;
    uint256 internal constant ZC_Z = 3;
    uint256 internal constant ZC_C = 4;
    uint256 internal constant LC_VALUE = 5;
    uint256 internal constant LIVE = 6;
    uint256 internal constant MASKED = 7;
    uint256 internal constant SIGMA = 8;
    uint256 internal constant VALUE = 9;
    uint256 internal constant GAMMA = 10;
    uint256 internal constant ANCHOR = 11;
    uint256 internal constant BITS = 12;
    uint256 internal constant WORDS = 13;
    uint256 internal constant WHIR_CLAIM = 14;
    uint256 internal constant WHIR_LAST = 15;
    uint256 internal constant SCALARS = 16;

    // Arrays.
    uint256 internal constant MLV = 0;
    uint256 internal constant R_REST = 1;
    uint256 internal constant RR = 2;
    uint256 internal constant SKIP = 3;
    uint256 internal constant RHO = 4;
    uint256 internal constant ER = 5;
    uint256 internal constant ECOL = 6;
    uint256 internal constant STACK_POINT = 7;
    uint256 internal constant POINT = 8;
    uint256 internal constant ANCHOR_POINT = 9;
    uint256 internal constant GAMMAS = 10;
    uint256 internal constant WHIR_CHALLENGES = 11;
    uint256 internal constant WHIR_EQ_COEFFS = 12;
    uint256 internal constant WHIR_OOD = 13;
    uint256 internal constant WHIR_POSITIONS = 14;
    uint256 internal constant WHIR_COEFFS = 15;
    uint256 internal constant CLAIMS = 16;
    uint256 internal constant CLAIMED = 17;
    uint256 internal constant ARRAYS = 18;

    // Byte strings.
    uint256 internal constant TR_PENDING = 0;
    uint256 internal constant CHILD_PENDING = 1;
    uint256 internal constant Z_PARTIAL = 2;
    uint256 internal constant EVALS = 3;
    uint256 internal constant GATHER = 4;
    uint256 internal constant CAP = 5;
    uint256 internal constant ACC = 6;
    uint256 internal constant WHIR_POINTS = 7;
    uint256 internal constant BYTES = 8;

    error WrongStage();

    /// A fresh state at `stage` for the statement with digest `digest`.
    function fresh(uint256 stage, bytes32 digest) internal pure returns (Carry memory n) {
        n.stage = stage;
        n.digest = digest;
        n.v = new uint256[](SCALARS);
        n.a = new uint256[][](ARRAYS);
        n.b = new bytes[](BYTES);
    }

    /// Where `b` sits in calldata.
    function at(bytes calldata b) internal pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }

    /// The `len` bytes of calldata at `from`.
    function slice(uint256 from, uint256 len) internal pure returns (bytes memory out) {
        out = new bytes(len);
        assembly ("memory-safe") {
            calldatacopy(add(out, 0x20), from, len)
        }
    }

    /// A transcript at chaining value `h` with the pending bytes `pending`.
    function transcript(uint256 h, bytes calldata pending, uint256 capacity) internal pure returns (uint256 tr) {
        assembly ("memory-safe") {
            tr := mload(0x40)
            mstore(0x40, add(tr, add(capacity, 128)))
            mstore(tr, h)
            mstore(add(tr, 0x20), pending.length)
            calldatacopy(add(tr, 0x40), pending.offset, pending.length)
        }
    }

    /// The chaining value and pending bytes of the transcript `tr`.
    function saved(uint256 tr) internal pure returns (uint256 h, bytes memory pending) {
        uint256 len;
        assembly ("memory-safe") {
            h := mload(tr)
            len := mload(add(tr, 0x20))
        }
        pending = new bytes(len);
        assembly ("memory-safe") {
            mcopy(add(pending, 0x20), add(tr, 0x40), len)
        }
    }

    /// Records in `n` what the last equation of an opening needs: the state `st` of the opening,
    /// whose claim had `points` points over `m` variables after `ood` out-of-domain points.
    function saveWhir(Carry memory n, WhirState memory st, uint256 ood, uint256 points, uint256 m) internal pure {
        n.v[WHIR_CLAIM] = st.claim;
        n.v[WHIR_LAST] = st.last;
        n.a[WHIR_CHALLENGES] = st.challenges;
        n.a[WHIR_EQ_COEFFS] = st.eqCoeffs;
        uint256 total;
        for (uint256 k = 0; k < st.eqCount; ++k) {
            if (k < ood || k >= ood + points) total += st.eqPoints[k].length;
        }
        uint256[] memory flat = new uint256[](total);
        bytes memory packed = new bytes(16 * points * m);
        uint256 f;
        for (uint256 k = 0; k < st.eqCount; ++k) {
            uint256[] memory z = st.eqPoints[k];
            if (k < ood || k >= ood + points) {
                for (uint256 i = 0; i < z.length; ++i) {
                    flat[f++] = z[i];
                }
            } else {
                uint256 dst = W.data(packed) + 16 * m * (k - ood);
                assembly ("memory-safe") {
                    for { let i := 0 } lt(i, m) { i := add(i, 1) } {
                        let w := add(dst, shl(4, i))
                        mstore(w, or(shl(128, mload(add(add(z, 0x20), shl(5, i)))), shr(128, shl(128, mload(w)))))
                    }
                }
            }
        }
        n.a[WHIR_OOD] = flat;
        n.b[WHIR_POINTS] = packed;
        total = 0;
        for (uint256 r = 0; r < st.positions.length; ++r) {
            total += st.positions[r].length;
        }
        uint256[] memory positions = new uint256[](total);
        uint256[] memory coeffs = new uint256[](total);
        f = 0;
        for (uint256 r = 0; r < st.positions.length; ++r) {
            for (uint256 q = 0; q < st.positions[r].length; ++q) {
                positions[f] = st.positions[r][q];
                coeffs[f++] = st.coeffs[r][q];
            }
        }
        n.a[WHIR_POSITIONS] = positions;
        n.a[WHIR_COEFFS] = coeffs;
    }

    /// The state of an opening under the schedule `rounds` that `saveWhir` recorded in `c`, whose
    /// claim had `points` points.
    function loadWhir(Carry calldata c, bytes memory rounds, uint256 points) internal pure returns (WhirState memory st) {
        uint256 n = rounds.length / 7;
        uint256 m = W.read(rounds, 0, 1);
        st.claim = c.v[WHIR_CLAIM];
        st.last = c.v[WHIR_LAST];
        st.challenges = c.a[WHIR_CHALLENGES];
        st.eqCoeffs = c.a[WHIR_EQ_COEFFS];
        st.eqCount = st.eqCoeffs.length;
        st.eqPoints = new uint256[][](st.eqCount);
        uint256[] memory flat = c.a[WHIR_OOD];
        uint256 packed = at(c.b[WHIR_POINTS]);
        uint256 k;
        uint256 f;
        for (uint256 r = 0; r < n; ++r) {
            uint256 vars = W.read(rounds, 7 * r, 1);
            uint256 ood = W.read(rounds, 7 * r + 5, 1);
            for (uint256 j = 0; j < ood; ++j) {
                uint256[] memory z = new uint256[](vars);
                for (uint256 i = 0; i < vars; ++i) {
                    z[i] = flat[f++];
                }
                st.eqPoints[k++] = z;
            }
            if (r == 0) {
                for (uint256 j = 0; j < points; ++j) {
                    uint256[] memory z = new uint256[](m);
                    uint256 src = packed + 16 * m * j;
                    assembly ("memory-safe") {
                        for { let i := 0 } lt(i, m) { i := add(i, 1) } {
                            mstore(add(add(z, 0x20), shl(5, i)), shr(128, calldataload(add(src, shl(4, i)))))
                        }
                    }
                    st.eqPoints[k++] = z;
                }
            }
        }
        if (k != st.eqCount || f != flat.length || c.b[WHIR_POINTS].length != 16 * m * points) revert WrongStage();
        st.positions = new uint256[][](n);
        st.coeffs = new uint256[][](n);
        uint256[] memory positions = c.a[WHIR_POSITIONS];
        uint256[] memory coeffs = c.a[WHIR_COEFFS];
        f = 0;
        for (uint256 r = 0; r + 1 < n; ++r) {
            uint256 queries = W.read(rounds, 7 * r + 3, 2);
            st.positions[r] = new uint256[](queries);
            st.coeffs[r] = new uint256[](queries);
            for (uint256 q = 0; q < queries; ++q) {
                st.positions[r][q] = positions[f];
                st.coeffs[r][q] = coeffs[f++];
            }
        }
        if (f != positions.length) revert WrongStage();
    }
}
