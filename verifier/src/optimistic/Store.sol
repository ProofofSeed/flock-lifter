// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {CodeStore} from "./CodeStore.sol";

/// Deploys contracts that hold data, one chunk per call.
contract Store {
    /// Deploys a contract holding `data` and returns its address.
    function put(bytes calldata data) external returns (address) {
        return CodeStore.write(data);
    }
}
