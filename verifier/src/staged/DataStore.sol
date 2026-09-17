// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Constant tables kept as the code of a contract that cannot run: a leading `STOP`, then the bytes.
library DataStore {
    /// The bytes held at `at`.
    function read(address at) internal view returns (bytes memory data) {
        uint256 len = at.code.length - 1;
        data = new bytes(len);
        assembly ("memory-safe") {
            extcodecopy(at, add(data, 0x20), 1, len)
        }
    }
}
