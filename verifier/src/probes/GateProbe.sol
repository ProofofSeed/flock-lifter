// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {FiatShamir, OutputShape} from "../FiatShamir.sol";

/// Exposes the Fiat-Shamir gate alone to the Rust harness.
contract GateProbe {
    /// Runs the gate over `n` responses: `data` holds their published words, then their unopened
    /// digests.
    function gate(bytes calldata output, uint256 counts, bytes calldata binding, uint256 n, bytes calldata data)
        external
        pure
        returns (bool)
    {
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        FiatShamir.GateArgs memory a;
        a.bindingLen = binding.length;
        a.n = n;
        a.nIo = (data.length - 32 * n) / (16 * n);
        uint256 o;
        uint256 b;
        uint256 d;
        assembly ("memory-safe") {
            o := output.offset
            b := binding.offset
            d := data.offset
        }
        a.outputAt = o;
        a.bindingAt = b;
        a.wordsAt = d;
        a.unopenedAt = d + 16 * a.nIo * n;
        FiatShamir.gate(s, a);
        return true;
    }
}
