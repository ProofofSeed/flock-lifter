// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "./GF2.sol";

/// Readers of the calldata encoding in `crates/evm/src/calldata.rs`, each taking an absolute
/// calldata offset.
library Calldata {
    /// A big-endian field element.
    function f128(uint256 p) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(128, calldataload(p))
        }
    }

    /// A field element in Flock's native layout.
    function native(uint256 p) internal pure returns (uint256) {
        uint256 x;
        assembly ("memory-safe") {
            x := shr(128, calldataload(p))
        }
        return GF2.fromNative(x);
    }

    /// An extension element, `c1` then `c0`, which is exactly its word.
    function f256(uint256 p) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := calldataload(p)
        }
    }

    /// A proof-of-work nonce.
    function nonce(uint256 p) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(192, calldataload(p))
        }
    }

    /// A big-endian `u32`.
    function u32(uint256 p) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(224, calldataload(p))
        }
    }
}
