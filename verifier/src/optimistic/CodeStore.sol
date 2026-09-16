// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Bytes kept on chain as the code of contracts that cannot run: each holds a chunk after a
/// leading `STOP`, so that a program larger than a deployable contract can still be read.
library CodeStore {
    /// Data bytes per holding contract.
    uint256 internal constant CHUNK = 24000;

    error Create();

    /// Deploys a contract holding `data`.
    function write(bytes memory data) internal returns (address at) {
        uint256 n = data.length + 1;
        bytes memory init = abi.encodePacked(
            hex"61", uint16(n), hex"80600c6000396000f3", hex"00", data
        );
        assembly ("memory-safe") {
            at := create(0, add(init, 0x20), mload(init))
        }
        if (at == address(0)) revert Create();
    }

    /// Deploys `data` in chunks, returning the holding contracts in order.
    function writeAll(bytes memory data) internal returns (address[] memory chunks) {
        chunks = new address[]((data.length + CHUNK - 1) / CHUNK);
        for (uint256 i = 0; i < chunks.length; ++i) {
            uint256 from = i * CHUNK;
            uint256 len = data.length - from < CHUNK ? data.length - from : CHUNK;
            bytes memory part = new bytes(len);
            for (uint256 j = 0; j < len; ++j) {
                part[j] = data[from + j];
            }
            chunks[i] = write(part);
        }
    }

    /// Copies `len` bytes at `offset` of the data held in `chunks` to memory at `dst`; bytes
    /// past the data read as zero.
    function read(address[] memory chunks, uint256 offset, uint256 len, uint256 dst) internal view {
        uint256 n = chunks.length;
        assembly ("memory-safe") {
            let chunkSize := 24000
            for {} gt(len, 0) {} {
                let c := div(offset, chunkSize)
                let within := mod(offset, chunkSize)
                let take := sub(chunkSize, within)
                if gt(take, len) { take := len }
                switch lt(c, n)
                case 1 {
                    let a := mload(add(add(chunks, 0x20), shl(5, c)))
                    extcodecopy(a, dst, add(within, 1), take)
                }
                default {
                    calldatacopy(dst, calldatasize(), take)
                }
                dst := add(dst, take)
                offset := add(offset, take)
                len := sub(len, take)
            }
        }
    }

    /// The valid jump destinations of the program of `codeLen` bytes held in `chunks`, as a
    /// bitmap with bit `i % 8` of byte `i / 8` set for destination `i`, deployed as held data.
    function buildJumps(address[] memory chunks, uint256 codeLen) internal returns (address) {
        bytes memory code = new bytes(codeLen);
        bytes memory bits = new bytes((codeLen + 7) / 8);
        read(chunks, 0, codeLen, _ptr(code));
        assembly ("memory-safe") {
            let c := add(code, 0x20)
            let b := add(bits, 0x20)
            for { let i := 0 } lt(i, codeLen) {} {
                let op := byte(0, mload(add(c, i)))
                switch op
                case 0x5b {
                    let slot := add(b, shr(3, i))
                    mstore8(slot, or(byte(0, mload(slot)), shl(and(i, 7), 1)))
                    i := add(i, 1)
                }
                default {
                    switch and(gt(op, 0x5f), lt(op, 0x80))
                    case 1 { i := add(i, sub(op, 0x5e)) }
                    default { i := add(i, 1) }
                }
            }
        }
        return write(bits);
    }

    /// Whether `dest` is a valid jump destination in the bitmap held at `jumps`.
    function isJump(address jumps, uint256 dest) internal view returns (bool ok) {
        assembly ("memory-safe") {
            let p := mload(0x40)
            mstore(p, 0)
            extcodecopy(jumps, p, add(shr(3, dest), 1), 1)
            ok := and(shr(and(dest, 7), byte(0, mload(p))), 1)
        }
    }

    function _ptr(bytes memory b) private pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(b, 0x20)
        }
    }
}
