// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants, LigeritoConfig} from "../Constants.sol";
import {Staged, State} from "./Staged.sol";

/// The Ligerito schedule of a commitment, carried in the staged state.
library Config {
    /// Writes the schedule of a commitment to `2^m` bits into `st`.
    function fill(State memory st, uint256 m, bool slim) internal pure {
        LigeritoConfig memory c = Constants.ligerito(m, slim);
        st.v[Staged.STEPS] = c.steps;
        st.v[Staged.INITIAL_K] = c.initialK;
        st.a[Staged.CFG_RATES] = c.logInvRates;
        st.a[Staged.CFG_KS] = c.recursiveKs;
        st.a[Staged.CFG_QUERIES] = c.queries;
        st.a[Staged.CFG_GRINDING] = c.grindingBits;
        st.a[Staged.CFG_CLAIM_BITS] = c.claimBits;
        st.a[Staged.CFG_CONS_BITS] = c.consistencyBits;
        st.a[Staged.CFG_OOD] = c.oodSamples;
        st.a[Staged.CFG_BLOCK_LENS] = c.logBlockLens;
        uint256 total;
        for (uint256 i = 0; i < c.depths.length; ++i) {
            total += 1 + c.depths[i].length;
        }
        uint256[] memory flat = new uint256[](total);
        uint256 at;
        for (uint256 i = 0; i < c.depths.length; ++i) {
            flat[at++] = c.depths[i].length;
            for (uint256 k = 0; k < c.depths[i].length; ++k) {
                flat[at++] = c.depths[i][k];
            }
        }
        st.a[Staged.CFG_DEPTHS] = flat;
    }

    /// The stratum depths of `level`.
    function depths(State memory st, uint256 level) internal pure returns (uint256[] memory d) {
        uint256[] memory flat = st.a[Staged.CFG_DEPTHS];
        uint256 at;
        for (uint256 i = 0; i < level; ++i) {
            at += 1 + flat[at];
        }
        d = new uint256[](flat[at]);
        for (uint256 k = 0; k < d.length; ++k) {
            d[k] = flat[at + 1 + k];
        }
    }

    /// The depth of `level`'s cap.
    function capDepth(State memory st, uint256 level) internal pure returns (uint256) {
        uint256[] memory flat = st.a[Staged.CFG_DEPTHS];
        uint256 at;
        for (uint256 i = 0; i < level; ++i) {
            at += 1 + flat[at];
        }
        return flat[at + 1];
    }
}
