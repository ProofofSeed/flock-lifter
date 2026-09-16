// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// The shape of the lifted statement's output: word counts per width, and where each width's
/// words start in its serialisation.
struct OutputShape {
    uint256[3] counts;
    uint256[3] at;
    uint256 payload;
    uint256 length;
}

/// ZKBoo's global Fiat-Shamir gate, run over the words the chunks publish: the challenge
/// entropy is recomputed from every response's opened view digests and output shares and the
/// unopened digest, and the challenges it derives must be the published ones.
library FiatShamir {
    bytes15 internal constant TAG_CHALLENGE = "ZKBOO-CHALLENGE";
    bytes9 internal constant TAG_PRG = "ZKBOO-PRG";

    error Output();
    error Challenge();
    error Gate();

    function minLeLength(uint256 x) internal pure returns (uint256 n) {
        for (; x > 0; x >>= 8) {
            ++n;
        }
    }

    /// Checks that `output` is the serialisation of words with `c8`, `c32` and `c64` words of
    /// each width (ZKBoo's flags byte, then per non-empty width its count in minimal
    /// little-endian bytes and the words), and returns its shape.
    function shape(bytes calldata output, uint256 c8, uint256 c32, uint256 c64)
        internal
        pure
        returns (OutputShape memory s)
    {
        s.counts = [c8, c32, c64];
        uint256[3] memory widths = [uint256(1), 4, 8];
        uint256 flags = (c8 > 0 ? 1 : 0) | (c32 > 0 ? 4 : 0) | (c64 > 0 ? 8 : 0);
        if (output.length == 0 || uint8(output[0]) != flags) revert Output();
        uint256 at = 1;
        for (uint256 k = 0; k < 3; ++k) {
            uint256 count = s.counts[k];
            uint256 n = minLeLength(count);
            for (uint256 i = 0; i < n; ++i) {
                if (at + i >= output.length || uint8(output[at + i]) != (count >> (8 * i)) & 0xff) revert Output();
            }
            at += n;
            s.at[k] = at;
            at += count * widths[k];
        }
        if (at != output.length) revert Output();
        s.length = at;
        s.payload = c8 + 4 * c32 + 8 * c64;
    }

    /// Writes a share's serialisation at `dst`: the header of `output` with the payload taken
    /// from `src`, and returns the byte just after it.
    function writeShare(OutputShape memory s, uint256 outputAt, uint256 src, uint256 dst, bool fromMemory)
        internal
        pure
        returns (uint256)
    {
        uint256 len = s.length;
        uint256 a0 = s.at[0];
        uint256 a1 = s.at[1];
        uint256 a2 = s.at[2];
        uint256 l0 = s.counts[0];
        uint256 l1 = 4 * s.counts[1];
        uint256 l2 = 8 * s.counts[2];
        assembly ("memory-safe") {
            calldatacopy(dst, outputAt, len)
            switch fromMemory
            case 0 {
                calldatacopy(add(dst, a0), src, l0)
                calldatacopy(add(dst, a1), add(src, l0), l1)
                calldatacopy(add(dst, a2), add(src, add(l0, l1)), l2)
            }
            default {
                mcopy(add(dst, a0), src, l0)
                mcopy(add(dst, a1), add(src, l0), l1)
                mcopy(add(dst, a2), add(src, add(l0, l1)), l2)
            }
        }
        return dst + len;
    }

    /// The expected output's words, concatenated in width order.
    function payloadOf(OutputShape memory s, uint256 outputAt) internal pure returns (uint256 buf) {
        buf = allocate(s.payload + 32);
        uint256 dst = buf;
        uint256[3] memory lens = [s.counts[0], 4 * s.counts[1], 8 * s.counts[2]];
        for (uint256 k = 0; k < 3; ++k) {
            uint256 from = outputAt + s.at[k];
            uint256 len = lens[k];
            assembly ("memory-safe") {
                calldatacopy(dst, from, len)
            }
            dst += len;
        }
    }

    function allocate(uint256 n) internal pure returns (uint256 ptr) {
        assembly ("memory-safe") {
            ptr := mload(0x40)
            mstore(0x40, add(ptr, and(add(n, 31), not(31))))
        }
    }

    function uint64le(uint256 x) internal pure returns (uint256 r) {
        for (uint256 i = 0; i < 8; ++i) {
            r |= ((x >> (8 * i)) & 0xff) << (8 * (7 - i));
        }
    }

    /// Where a lift's gate inputs sit in calldata.
    struct GateArgs {
        uint256 outputAt;
        uint256 bindingAt;
        uint256 bindingLen;
        uint256 n;
        uint256 nIo;
        uint256 wordsAt;
        uint256 unopenedAt;
    }

    /// The gate's working state.
    struct GateIn {
        uint256 outputAt;
        uint256 n;
        uint256 nIo;
        uint256 wordsAt;
        uint256 unopenedAt;
        uint256 y;
        uint256 third;
    }

    /// Runs the gate over `n` responses whose published words start at `wordsAt` (`nIo` words
    /// each, native layout) and whose unopened digests start at `unopenedAt`.
    function gate(OutputShape memory s, GateArgs memory a) internal pure {
        GateIn memory g =
            GateIn(a.outputAt, a.n, a.nIo, a.wordsAt, a.unopenedAt, payloadOf(s, a.outputAt), allocate(s.payload + 32));
        uint256 pre = allocate(23 + a.bindingLen + a.n * 3 * (32 + s.length));
        uint256 tag = uint256(bytes32(TAG_CHALLENGE)) | (uint64le(a.bindingLen) << 72);
        uint256 bindingAt = a.bindingAt;
        uint256 bindingLen = a.bindingLen;
        assembly ("memory-safe") {
            mstore(pre, tag)
            calldatacopy(add(pre, 23), bindingAt, bindingLen)
        }
        uint256 at = pre + 23 + bindingLen;
        uint256[] memory challenges = new uint256[](a.n);
        for (uint256 i = 0; i < a.n; ++i) {
            (at, challenges[i]) = absorbResponse(s, g, i, at);
        }
        bytes32 entropy;
        assembly ("memory-safe") {
            entropy := keccak256(pre, sub(at, pre))
        }
        derive(entropy, challenges);
    }

    /// Writes the bytes response `i` contributes to the challenge entropy at `at`, its parties
    /// in the order its challenge rotates them into, and returns the end and the challenge.
    function absorbResponse(OutputShape memory s, GateIn memory g, uint256 i, uint256 at)
        internal
        pure
        returns (uint256, uint256 c)
    {
        uint256 ow = (g.nIo - 5) / 2;
        uint256 row = g.wordsAt + 16 * g.nIo * i;
        c = challengeOf(row);
        xorShares(g.third, g.y, row + 16 * 5, ow, s.payload);
        for (uint256 p = 0; p < 3; ++p) {
            uint256 who = (p + 3 - c) % 3;
            uint256 digestAt = who == 2 ? g.unopenedAt + 32 * i : row + 16 * (1 + 2 * who);
            assembly ("memory-safe") {
                calldatacopy(at, digestAt, 32)
            }
            if (who == 2) {
                at = writeShare(s, g.outputAt, g.third, at + 32, true);
            } else {
                at = writeShare(s, g.outputAt, row + 16 * (5 + who * ow), at + 32, false);
            }
        }
        return (at, c);
    }

    function challengeOf(uint256 row) internal pure returns (uint256 c) {
        uint256 w;
        assembly ("memory-safe") {
            w := shr(128, calldataload(row))
        }
        if (w == 0x01000000000000000000000000000000) return 0;
        if (w == 0x02000000000000000000000000000000) return 1;
        if (w == 0x04000000000000000000000000000000) return 2;
        revert Challenge();
    }

    /// `third = y ⊕ share0 ⊕ share1` over the payload, the shares read from calldata.
    function xorShares(uint256 third, uint256 y, uint256 sharesAt, uint256 ow, uint256 len) internal pure {
        assembly ("memory-safe") {
            let tmp := mload(0x40)
            calldatacopy(tmp, sharesAt, mul(32, ow))
            let off := mul(16, ow)
            for { let k := 0 } lt(k, len) { k := add(k, 32) } {
                let a := mload(add(y, k))
                let b := mload(add(tmp, k))
                let d := mload(add(add(tmp, off), k))
                mstore(add(third, k), xor(a, xor(b, d)))
            }
        }
    }

    /// Replays ZKBoo's challenge generator from `entropy` and compares every challenge.
    function derive(bytes32 entropy, uint256[] memory challenges) internal pure {
        bytes32 key = keccak256(abi.encodePacked(TAG_PRG, bytes8(uint64(uint64le(32))), entropy));
        uint256 counter;
        uint256 buf;
        uint256 pos = 32;
        uint256 current;
        uint256 used = 8;
        for (uint256 i = 0; i < challenges.length; ++i) {
            uint256 party = 3;
            while (party > 2) {
                if (used == 8) {
                    if (pos == 32) {
                        buf = uint256(keccak256(abi.encodePacked(TAG_PRG, key, bytes8(uint64(uint64le(counter))))));
                        ++counter;
                        pos = 0;
                    }
                    current = (buf >> (8 * (31 - pos))) & 0xff;
                    ++pos;
                    used = 0;
                }
                party = current & 3;
                current >>= 2;
                used += 2;
            }
            if (party != challenges[i]) revert Gate();
        }
    }
}
