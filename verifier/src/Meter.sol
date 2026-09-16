// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// Gas marks for the harness: each emits the gas left at the end of a phase.
library Meter {
    /// Emitted at the end of phase `id` with the gas left.
    event Phase(uint256 indexed id, uint256 gasLeft);

    function mark(uint256 id) internal {
        emit Phase(id, gasleft());
    }
}
