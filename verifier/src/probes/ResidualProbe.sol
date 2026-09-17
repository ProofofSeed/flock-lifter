// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "../Constants.sol";
import {GF2} from "../GF2.sol";
import {Residual} from "../Residual.sol";
import {Tensor} from "./Tensor.sol";

/// Exposes the residual library, beside the table-per-point evaluation it replaced, to the Rust
/// harness.
contract ResidualProbe {
    function consistency(uint256 logCols, uint256[] calldata qs, uint256[] calldata alpha, uint256[] calldata fixedPart, uint256[] calldata mu)
        external
        view
        returns (uint256 got, uint256 gas)
    {
        gas = gasleft();
        got = Residual.consistency(logCols, qs, GF2.eqTable(alpha), fixedPart, mu);
        gas -= gasleft();
    }

    function consistencyOld(uint256 logCols, uint256[] calldata qs, uint256[] calldata alpha, uint256[] calldata fixedPart, uint256[] calldata mu)
        external
        view
        returns (uint256 got, uint256 gas)
    {
        gas = gasleft();
        got = inducedBasis(logCols, qs, alpha, fixedPart, mu.length == 1 ? 0 : _log(mu.length), mu);
        gas -= gasleft();
    }

    function ringSwitch(uint256[] calldata ris, uint256[] calldata flatX, uint256[] calldata flatEq, uint256[] calldata gammas, uint256[] calldata mu)
        external
        view
        returns (uint256 got, uint256 gas)
    {
        (uint256[][] memory xs, uint256[][] memory eqs) = _unflatten(flatX, flatEq, gammas.length);
        gas = gasleft();
        got = Residual.ringSwitch(ris, xs, eqs, gammas, mu);
        gas -= gasleft();
    }

    function ringSwitchOld(uint256[] calldata ris, uint256[] calldata flatX, uint256[] calldata flatEq, uint256[] calldata gammas, uint256[] calldata mu)
        external
        view
        returns (uint256 got, uint256 gas)
    {
        (uint256[][] memory xs, uint256[][] memory eqs) = _unflatten(flatX, flatEq, gammas.length);
        gas = gasleft();
        got = _old(ris, xs, eqs, gammas, mu);
        gas -= gasleft();
    }

    function _old(uint256[] memory ris, uint256[][] memory xs, uint256[][] memory eqs, uint256[] memory gammas, uint256[] memory mu)
        private
        pure
        returns (uint256 got)
    {
        Tensor.Work memory w = Tensor.work();
        for (uint256 c = 0; c < gammas.length; ++c) {
            (uint256[] memory c0, uint256[] memory c1) = Tensor.prefix(xs[c], 1, ris, w);
            Tensor.foldTable(eqs[c], w);
            for (uint256 y = 0; y < mu.length; ++y) {
                uint256 e = Tensor.finish(c0, c1, xs[c], 1 + ris.length, y, w);
                got ^= GF2.mul256(GF2.mul256By128(e, gammas[c]), mu[y]);
            }
        }
    }

    function _unflatten(uint256[] calldata flatX, uint256[] calldata flatEq, uint256 n)
        private
        pure
        returns (uint256[][] memory xs, uint256[][] memory eqs)
    {
        xs = new uint256[][](n);
        eqs = new uint256[][](n);
        uint256 len = flatX.length / n;
        for (uint256 c = 0; c < n; ++c) {
            xs[c] = flatX[c * len:(c + 1) * len];
            eqs[c] = flatEq[c * 128:(c + 1) * 128];
        }
    }

    function _log(uint256 n) private pure returns (uint256 r) {
        while ((1 << r) < n) {
            ++r;
        }
    }

    function inducedBasis(
        uint256 logCols,
        uint256[] memory qs,
        uint256[] memory alpha,
        uint256[] memory fixedPart,
        uint256 ext,
        uint256[] memory mu
    ) private pure returns (uint256 total) {
        uint256[] memory weights = GF2.eqTable(alpha);
        uint256 f = fixedPart.length;
        uint256[] memory w = new uint256[](logCols);
        uint256[] memory v = new uint256[](mu.length);
        bytes memory table = Constants.SUBSPACE;
        for (uint256 q = 0; q < qs.length; ++q) {
            _subspace(w, qs[q], table);
            total ^= GF2.mul256(_prefix(weights[q], fixedPart, w, f), _suffixForm(mu, v, w, f, ext));
        }
    }

    /// `weight·Π_{k < f} (1 + fixed[k]·(1 + w[k]))`.
    function _prefix(uint256 weight, uint256[] memory fixedPart, uint256[] memory w, uint256 f)
        internal
        pure
        returns (uint256 prefix)
    {
        prefix = weight;
        for (uint256 k = 0; k < f; ++k) {
            prefix = GF2.mul256(prefix, 1 ^ GF2.mul256By128(fixedPart[k], 1 ^ w[k]));
        }
    }

    /// `Σ_y μ_y·Π_{j ∈ y} w[f + j]`, by folding the top variable first.
    function _suffixForm(uint256[] memory mu, uint256[] memory v, uint256[] memory w, uint256 f, uint256 ext)
        internal
        pure
        returns (uint256)
    {
        for (uint256 y = 0; y < mu.length; ++y) {
            v[y] = mu[y];
        }
        for (uint256 j = ext; j > 0; --j) {
            uint256 half = 1 << (j - 1);
            uint256 s = w[f + j - 1];
            for (uint256 y = 0; y < half; ++y) {
                v[y] ^= GF2.mul256By128(v[y + half], s);
            }
        }
        return v[0];
    }

    /// `w[k] = s_k(q)/s_k(v_k)` for every `k`, from the table of the normalised subspace
    /// polynomials at the basis elements: each is linear in the bits of `q`.
    function _subspace(uint256[] memory w, uint256 q, bytes memory table) private pure {
        uint256 n = w.length;
        assembly ("memory-safe") {
            let dst := add(w, 0x20)
            for { let k := 0 } lt(k, n) { k := add(k, 1) } {
                mstore(add(dst, shl(5, k)), 0)
            }
            let src := add(table, 0x20)
            for { let b := 0 } lt(b, 32) { b := add(b, 1) } {
                if and(shr(b, q), 1) {
                    for { let k := 0 } lt(k, n) { k := add(k, 1) } {
                        let slot := add(dst, shl(5, k))
                        let entry := shr(128, mload(add(src, mul(16, add(mul(k, 32), b)))))
                        mstore(slot, xor(mload(slot), entry))
                    }
                }
            }
        }
    }

}
