// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "../GF2.sol";
import {Opening} from "../Opening.sol";
import {Staged, State} from "./Staged.sol";

/// The Ligerito level challenges held in the staged state, and what the residuals derive from them.
library Walk {
    /// The challenges the residual points fix, from level `start` on, with the initial ones when
    /// `withInitial` and `start` is zero.
    function originalChallenges(State memory st, uint256 start, bool withInitial)
        internal
        pure
        returns (uint256[] memory out)
    {
        uint256 steps = st.v[Staged.STEPS];
        bool initial = withInitial && start == 0;
        uint256[] memory init = st.a[Staged.INITIAL];
        uint256 len = initial ? init.length : 0;
        for (uint256 l = start; l < steps; ++l) {
            len += st.a[Staged.LEVELS + l].length - 1;
        }
        out = new uint256[](len);
        uint256 at;
        if (initial) {
            for (uint256 k = 0; k < init.length; ++k) {
                out[at++] = init[k];
            }
        }
        for (uint256 l = start; l < steps; ++l) {
            uint256[] memory level = st.a[Staged.LEVELS + l];
            for (uint256 k = 1; k < level.length; ++k) {
                out[at++] = level[k];
            }
        }
    }

    /// The challenges an out-of-domain sample introduced at `split` fixes.
    function splitChallenges(State memory st, uint256 split) internal pure returns (uint256[] memory out) {
        uint256 steps = st.v[Staged.STEPS];
        uint256 len = st.a[Staged.LEVELS + split].length;
        for (uint256 l = split + 1; l < steps; ++l) {
            len += st.a[Staged.LEVELS + l].length - 1;
        }
        out = new uint256[](len);
        uint256 at;
        uint256[] memory first = st.a[Staged.LEVELS + split];
        for (uint256 k = 0; k < first.length; ++k) {
            out[at++] = first[k];
        }
        for (uint256 l = split + 1; l < steps; ++l) {
            uint256[] memory level = st.a[Staged.LEVELS + l];
            for (uint256 k = 1; k < level.length; ++k) {
                out[at++] = level[k];
            }
        }
    }

    /// `Π_{l ≥ start} (1 + r_l·(1 + u))` over the first challenge of each level.
    function factorProduct(State memory st, uint256 start) internal pure returns (uint256 acc) {
        acc = 1;
        uint256 onePlusU = (uint256(1) << 128) | 1;
        uint256 steps = st.v[Staged.STEPS];
        for (uint256 l = start; l < steps; ++l) {
            acc = GF2.mul256(acc, 1 ^ GF2.mul256(st.a[Staged.LEVELS + l][0], onePlusU));
        }
    }

    /// `Σ_y μ_y·O[y]` for `O` the out-of-domain part of the residual.
    function oodDot(State memory st, uint256[] memory original) internal pure returns (uint256 got) {
        uint256[] memory mu = st.a[Staged.MU];
        uint256[] memory residual = new uint256[](mu.length);
        for (uint256 o = 0; o < st.v[Staged.NOOD]; ++o) {
            uint256[] memory values = _oodValues(st, original, o);
            for (uint256 y = 0; y < residual.length; ++y) {
                residual[y] ^= values[y];
            }
        }
        for (uint256 y = 0; y < residual.length; ++y) {
            got ^= GF2.mul256(residual[y], mu[y]);
        }
    }

    function _oodValues(State memory st, uint256[] memory original, uint256 o) private pure returns (uint256[] memory) {
        uint256 split = st.a[Staged.OOD_SPLIT][o];
        uint256[] memory fixedPart;
        uint256 scale;
        if (split == type(uint256).max) {
            fixedPart = original;
            scale = factorProduct(st, 0);
        } else {
            fixedPart = splitChallenges(st, split);
            scale = factorProduct(st, split + 1);
        }
        scale = GF2.mul256By128(scale, st.a[Staged.OOD_BETA][o]);
        return Opening.eqResidual(st.a[Staged.OOD_POINT + o], fixedPart, st.v[Staged.EXT], scale);
    }
}
