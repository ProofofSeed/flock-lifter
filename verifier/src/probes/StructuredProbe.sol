// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Structured} from "../Structured.sol";

/// Exposes the structured part, whole and in resumable pieces, to the Rust harness.
contract StructuredProbe {
    function whole(Structured.Input memory c) external pure returns (uint256) {
        return Structured.value(c, Structured.work());
    }

    /// The value computed with the kernel carried across fresh buffers at each of `cuts`.
    function pieces(Structured.Input memory c, uint256[] memory cuts) external pure returns (uint256) {
        uint256[] memory work = Structured.work();
        uint256[] memory accs = new uint256[](4);
        accs[3] = Structured.setup(c, work);
        (uint256[] memory kernel, uint256[] memory pairs) = _save(work);
        uint256 from;
        for (uint256 i = 0; i <= cuts.length; ++i) {
            uint256 to = i < cuts.length ? cuts[i] : 24;
            (kernel, pairs) = _span(c, accs, kernel, pairs, from, to);
            from = to;
        }
        work = Structured.work();
        _load(work, kernel, pairs);
        (uint256 v0, uint256 col0) = Structured.last(c, work);
        return Structured.combine(c, accs[0] ^ v0, accs[1], accs[2], accs[3], col0);
    }

    function _span(
        Structured.Input memory c,
        uint256[] memory accs,
        uint256[] memory kernel,
        uint256[] memory pairs,
        uint256 from,
        uint256 to
    ) private pure returns (uint256[] memory, uint256[] memory) {
        uint256[] memory work = Structured.work();
        _load(work, kernel, pairs);
        (uint256 dv, uint256 drc, uint256 dw) = Structured.rounds(c, work, from, to);
        accs[0] ^= dv;
        accs[1] ^= drc;
        accs[2] ^= dw;
        return _save(work);
    }

    function _save(uint256[] memory work) private pure returns (uint256[] memory kernel, uint256[] memory pairs) {
        kernel = new uint256[](1600);
        pairs = new uint256[](64);
        assembly ("memory-safe") {
            let cx := add(work, 0x20)
            mcopy(add(kernel, 0x20), mload(add(cx, 0x20)), shl(5, 1600))
            mcopy(add(pairs, 0x20), mload(add(cx, 0x180)), shl(5, 64))
        }
    }

    function _load(uint256[] memory work, uint256[] memory kernel, uint256[] memory pairs) private pure {
        assembly ("memory-safe") {
            let cx := add(work, 0x20)
            mcopy(mload(add(cx, 0x20)), add(kernel, 0x20), shl(5, 1600))
            mcopy(mload(add(cx, 0x180)), add(pairs, 0x20), shl(5, 64))
        }
    }
}
