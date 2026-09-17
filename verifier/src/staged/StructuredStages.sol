// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Structured} from "../Structured.sol";
import {IStage, Staged, State} from "./Staged.sol";

/// The structured parts of the matrix claims in items, 26 per claim: the pairing weights and
/// the kernel's start, the 24 rounds of the fold, and the last pairing, which leaves the claim's
/// running value minus its structured part.
contract StructuredStages is IStage {
    uint256 internal constant CLAIM_WORDS = 112;
    uint256 internal constant ROUNDS = 26;

    error Shape();

    function run(bytes calldata state, uint256 upto, bytes calldata)
        external
        pure
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.STRUCT, Staged.STRUCT);
        uint256 cursor = st.v[Staged.CURSOR];
        if (upto <= cursor || upto > st.v[Staged.ITEMS]) revert Shape();
        uint256[] memory work = Structured.work();
        uint256 item = cursor;
        while (item < upto) {
            item = _claim(st, work, item, upto);
        }
        assembly ("memory-safe") {
            mstore(0x40, mload(add(work, 0x20)))
        }
        st.v[Staged.CURSOR] = upto;
        uint256[] memory streams;
        if (upto == st.v[Staged.ITEMS]) {
            st.a[Staged.ACCS] = new uint256[](0);
            Staged.enter(st, Staged.M_MAIN, 1);
            streams = Staged.sequential(st.v[Staged.POS]);
        }
        return (Staged.save(st), Staged.request(st, streams));
    }

    function _input(State memory st, uint256 c) private pure returns (Structured.Input memory in_) {
        uint256[] memory claims = st.a[Staged.PACKED];
        uint256 b = c * CLAIM_WORDS;
        in_.alpha = claims[b];
        in_.beta = claims[b + 1];
        in_.skip = _slice(st.a[Staged.SKIPS], 64 * c, 64);
        in_.z = _slice(claims, b + 48, 64);
        in_.x = _slice(claims, b + 4, 22);
        in_.r = _slice(claims, b + 26, 22);
        in_.first = st.v[Staged.FIRST_KECCAK];
        in_.subs = st.v[Staged.KECCAK_SUBS];
    }

    function _slice(uint256[] memory v, uint256 from, uint256 len) private pure returns (uint256[] memory out) {
        out = new uint256[](len);
        for (uint256 k = 0; k < len; ++k) {
            out[k] = v[from + k];
        }
    }

    /// Runs claim `item / 26`'s items from `item` up to `upto`, returning the item it stopped at.
    function _claim(State memory st, uint256[] memory work, uint256 item, uint256 upto) private pure returns (uint256) {
        uint256 c = item / ROUNDS;
        uint256 j = item % ROUNDS;
        uint256 end = (c + 1) * ROUNDS < upto ? (c + 1) * ROUNDS : upto;
        Structured.Input memory in_ = _input(st, c);
        uint256[] memory accs = st.a[Staged.ACCS];
        if (j == 0) {
            accs[4 * c + 3] = Structured.setup(in_, work);
            ++j;
        } else {
            _load(st, work);
        }
        uint256 roundsEnd = end - c * ROUNDS < 25 ? end - c * ROUNDS : 25;
        if (j < roundsEnd) {
            (uint256 v, uint256 rc, uint256 w) = Structured.rounds(in_, work, j - 1, roundsEnd - 1);
            accs[4 * c] ^= v;
            accs[4 * c + 1] ^= rc;
            accs[4 * c + 2] ^= w;
            j = roundsEnd;
        }
        if (j == 25 && c * ROUNDS + j < end) {
            (uint256 v0, uint256 col0) = Structured.last(in_, work);
            st.a[Staged.VALUES][c] = st.a[Staged.PACKED][c * CLAIM_WORDS + 3]
                ^ Structured.combine(in_, accs[4 * c] ^ v0, accs[4 * c + 1], accs[4 * c + 2], accs[4 * c + 3], col0);
            st.a[Staged.KERNEL] = new uint256[](0);
            st.a[Staged.PAIRS] = new uint256[](0);
            return (c + 1) * ROUNDS;
        }
        _save(st, work);
        return c * ROUNDS + j;
    }

    /// Unpacks the kernel, two 128-bit values a word, and the pairing weights into the buffers.
    function _load(State memory st, uint256[] memory work) private pure {
        uint256[] memory kernel = st.a[Staged.KERNEL];
        uint256[] memory pairs = st.a[Staged.PAIRS];
        assembly ("memory-safe") {
            let cx := add(work, 0x20)
            let kp := mload(add(cx, 0x20))
            let src := add(kernel, 0x20)
            for { let i := 0 } lt(i, 800) { i := add(i, 1) } {
                let w := mload(add(src, shl(5, i)))
                mstore(add(kp, shl(6, i)), shr(128, w))
                mstore(add(kp, add(shl(6, i), 0x20)), and(w, 0xffffffffffffffffffffffffffffffff))
            }
            mcopy(mload(add(cx, 0x180)), add(pairs, 0x20), shl(5, 64))
        }
    }

    /// Packs the kernel, two 128-bit values a word, and the pairing weights into the state.
    function _save(State memory st, uint256[] memory work) private pure {
        uint256[] memory kernel = new uint256[](800);
        uint256[] memory pairs = new uint256[](64);
        assembly ("memory-safe") {
            let cx := add(work, 0x20)
            let kp := mload(add(cx, 0x20))
            let dst := add(kernel, 0x20)
            for { let i := 0 } lt(i, 800) { i := add(i, 1) } {
                mstore(add(dst, shl(5, i)), or(shl(128, mload(add(kp, shl(6, i)))), mload(add(kp, add(shl(6, i), 0x20)))))
            }
            mcopy(add(pairs, 0x20), mload(add(cx, 0x180)), shl(5, 64))
        }
        st.a[Staged.KERNEL] = kernel;
        st.a[Staged.PAIRS] = pairs;
    }
}
