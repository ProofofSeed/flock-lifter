// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {F} from "../wrap/F.sol";
import {K} from "../wrap/K.sol";

/// Exposes the wrap verifier's assembly kernels to the Rust harness, each beside the reference it
/// must agree with.
contract KProbe {
    function _ptr(uint256[] memory v) private pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(v, 0x20)
        }
    }

    /// The dot product of `a` and `b`, by the kernel and by the library, and the kernel's gas.
    function dot(uint256[] calldata a, uint256[] calldata b) external view returns (uint256 fast, uint256 slow, uint256 gasUsed) {
        uint256[] memory x = a;
        uint256[] memory y = b;
        uint256 g = gasleft();
        fast = K.dot(_ptr(x), _ptr(y), x.length);
        gasUsed = g - gasleft();
        slow = F.dot(x, y);
    }

    /// The equality table of `point`, by the kernel, and the kernel's gas.
    function eqTable(uint256[] calldata point) external view returns (uint256[] memory t, uint256 gasUsed) {
        uint256[] memory z = point;
        t = new uint256[](1 << z.length);
        uint256 g = gasleft();
        K.eqTable(_ptr(t), _ptr(z), z.length, 1);
        gasUsed = g - gasleft();
    }

    /// `a·b` over the extension, by the kernel and by the library, and the kernel's gas for `n` of them.
    function mul256(uint256 a, uint256 b, uint256 n) external view returns (uint256 fast, uint256 slow, uint256 gasUsed) {
        fast = K.mul256(a, b);
        slow = F.mul256(a, b);
        uint256 acc = a;
        uint256 g = gasleft();
        for (uint256 i = 0; i < n; ++i) {
            acc = K.mul256(acc, b);
        }
        gasUsed = g - gasleft();
    }

    /// `a^(2^k)` by the kernel and by the library, and the kernel's gas.
    function frob(uint256 a, uint256 k) external view returns (uint256 fast, uint256 slow, uint256 gasUsed) {
        uint256 g = gasleft();
        fast = K.frob(a, k);
        gasUsed = g - gasleft();
        slow = F.frob(a, k);
    }

    /// The gas of an equality product over `n` extension factors, and of `n` window lookups.
    function products(uint256 n) external view returns (uint256 eqGas, uint256 shiftGas) {
        uint256[] memory z = new uint256[](n);
        uint256[] memory y = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            z[i] = uint256(keccak256(abi.encode(i)));
            y[i] = uint256(keccak256(abi.encode(i, 1)));
        }
        uint256 g = gasleft();
        uint256 r = K.eqProduct256(z[0], _ptr(z), _ptr(y), n);
        eqGas = g - gasleft();
        uint256 windows = 7;
        uint256[] memory nt = new uint256[](16 * n * windows);
        for (uint256 i = 0; i < nt.length; i += 5) {
            nt[i] = r ^ i;
        }
        g = gasleft();
        r = K.shiftProduct(r, 0x5a5a5a5, _ptr(y), _ptr(nt), n, windows);
        shiftGas = g - gasleft();
    }
}
