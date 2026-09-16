// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "../GF2.sol";

/// Exposes the field library to the Rust harness.
contract GF2Probe {
    function mul(uint256 a, uint256 b) external pure returns (uint256) {
        return GF2.mul(a, b);
    }

    function sq(uint256 a) external pure returns (uint256) {
        return GF2.sq(a);
    }

    function inv(uint256 a) external pure returns (uint256) {
        return GF2.inv(a);
    }

    function mul256(uint256 a, uint256 b) external pure returns (uint256) {
        return GF2.mul256(a, b);
    }

    function fromNative(uint256 x) external pure returns (uint256) {
        return GF2.fromNative(x);
    }

    function eqTable(uint256[] calldata point) external pure returns (uint256[] memory) {
        return GF2.eqTable(point);
    }

    /// Gas of `n` multiplications and `n` squarings, measured inside one call.
    function meter(uint256 a, uint256 b, uint256 n) external view returns (uint256 mulGas, uint256 sqGas) {
        uint256 acc = a;
        uint256 g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = GF2.mul(acc, b);
        }
        mulGas = g - gasleft();
        g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = GF2.sq(acc);
        }
        sqGas = g - gasleft();
    }
}
