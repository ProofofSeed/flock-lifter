// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {F} from "../wrap/F.sol";

/// Exposes the wrap verifier's field library to the Rust harness.
contract FProbe {
    function mul(uint256 a, uint256 b) external pure returns (uint256) {
        return F.mul(a, b);
    }

    function sq(uint256 a) external pure returns (uint256) {
        return F.sq(a);
    }

    function mul256(uint256 a, uint256 b) external pure returns (uint256) {
        return F.mul256(a, b);
    }

    /// Gas of `n` multiplications, `n` squarings and `n` extension multiplications, measured inside one call.
    function meter(uint256 a, uint256 b, uint256 n) external view returns (uint256 mulGas, uint256 sqGas, uint256 extGas) {
        uint256 acc = a;
        uint256 g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = F.mul(acc, b);
        }
        mulGas = g - gasleft();
        g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = F.sq(acc);
        }
        sqGas = g - gasleft();
        acc |= b << 128;
        g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = F.mul256(acc, b);
        }
        extGas = g - gasleft();
    }
}
