// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {FlockWrap} from "../wrap/FlockWrap.sol";

/// The wrap verifier with an entry that stops after a given stage, so that the harness can compare
/// its stages with the mirror's one at a time.
contract WrapProbe is FlockWrap {
    function trace(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata lift, uint256 stop) external {
        _run(output, counts, binding, lift, stop);
    }
}
