// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "../GF2.sol";
import {Residual} from "../Residual.sol";
import {IStage, Staged, State} from "./Staged.sol";
import {Walk} from "./Walk.sol";

/// The ring-switch residual stage of a batched opening: each claim's ring-switching basis in items,
/// its rank expansion, its steps and its suffix points.
contract RingSwitchStages is IStage {
    error Shape();

    function run(bytes calldata state, uint256 upto, bytes calldata)
        external
        pure
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.RS, Staged.RS);
        if (upto <= st.v[Staged.CURSOR] || upto > st.v[Staged.ITEMS]) revert Shape();
        _rs(st, upto);
        return (Staged.save(st), Staged.request(st, new uint256[](0)));
    }

    /// The claim holding item `item`, and the item's index within it.
    function _locate(State memory st, uint256 item, uint256 points) private pure returns (uint256 c, uint256 j) {
        uint256[] memory ng = st.a[Staged.RS_NG];
        j = item;
        for (c = 0; c < ng.length; ++c) {
            uint256 size = 1 + (ng[c] > 5 ? ng[c] - 5 : 0) + points;
            if (j < size) return (c, j);
            j -= size;
        }
        revert Shape();
    }

    /// Where a claim's items stand within one call.
    struct Run {
        uint256 r;
        uint256 c;
        uint256 j;
        uint256 left;
        uint256 points;
        bool loaded;
        uint256[] original;
    }

    function _rs(State memory st, uint256 upto) private pure {
        Run memory run_;
        run_.points = 1 << st.v[Staged.EXT];
        run_.original = Walk.originalChallenges(st, 0, true);
        run_.r = Residual.region();
        (run_.c, run_.j) = _locate(st, st.v[Staged.CURSOR], run_.points);
        run_.left = upto - st.v[Staged.CURSOR];
        while (run_.left > 0) {
            _rsClaim(st, run_);
        }
        st.v[Staged.CURSOR] = upto;
        if (upto < st.v[Staged.ITEMS]) return;
        st.v[Staged.GOT] ^= GF2.mul256(st.v[Staged.RS_ACC], Walk.factorProduct(st, 0));
        st.a[Staged.WORK] = new uint256[](0);
        uint256 items;
        for (uint256 l = 0; l < st.v[Staged.NCONS]; ++l) {
            items += Walk.originalChallenges(st, st.a[Staged.CONS_START][l], false).length + 1;
        }
        Staged.enter(st, Staged.CONS, items);
    }

    /// Runs items of claim `run_.c` from its item `run_.j`, moving to the next claim when it ends.
    function _rsClaim(State memory st, Run memory run_) private pure {
        uint256[] memory x = st.a[Staged.CL_X + run_.c];
        uint256[] memory gq = new uint256[](run_.original.length);
        uint256[] memory gw = new uint256[](run_.original.length);
        (uint256 scalar, uint256 ng) = Residual.split(run_.original, x, gq, gw);
        uint256 a = ng < 5 ? ng : 5;
        uint256 stepsEnd = 1 + ng - a;
        uint256 size = stepsEnd + run_.points;
        if (run_.j == 0) {
            Residual.rank(run_.r, gq, gw, a);
            run_.loaded = true;
            run_.j = 1;
            --run_.left;
        } else if (!run_.loaded) {
            _loadColumns(run_.r, st.a[Staged.WORK]);
            run_.loaded = true;
        }
        while (run_.left > 0 && run_.j < stepsEnd) {
            Residual.step(run_.r, gq[a + run_.j - 1], gw[a + run_.j - 1]);
            ++run_.j;
            --run_.left;
        }
        if (run_.left > 0 && run_.j < size) {
            uint256 from = run_.j - stepsEnd;
            uint256 to = from + (run_.left < size - run_.j ? run_.left : size - run_.j);
            Residual.pointsBegin(run_.r, GF2.eqTable(_rdp(st, run_.c)));
            st.v[Staged.RS_PART] ^= Residual.points(
                run_.r, GF2.eqTable(Residual.suffixOf(run_.original, x)), st.a[Staged.MU], from, to
            );
            run_.left -= to - from;
            run_.j += to - from;
        }
        if (run_.j == size) {
            st.v[Staged.RS_ACC] ^= GF2.mul256By128(
                GF2.mul256(st.v[Staged.RS_PART], scalar), st.a[Staged.GAMMAS][run_.c]
            );
            st.v[Staged.RS_PART] = 0;
            ++run_.c;
            run_.j = 0;
            run_.loaded = false;
        } else {
            st.a[Staged.WORK] = _saveColumns(run_.r);
        }
    }

    function _rdp(State memory st, uint256 c) private pure returns (uint256[] memory r) {
        r = new uint256[](7);
        for (uint256 k = 0; k < 7; ++k) {
            r[k] = st.a[Staged.RDP][7 * c + k];
        }
    }

    function _loadColumns(uint256 r, uint256[] memory cols) private pure {
        uint256 at = Residual.columns(r);
        assembly ("memory-safe") {
            mcopy(at, add(cols, 0x20), 0x1000)
        }
    }

    function _saveColumns(uint256 r) private pure returns (uint256[] memory cols) {
        cols = new uint256[](128);
        uint256 at = Residual.columns(r);
        assembly ("memory-safe") {
            mcopy(add(cols, 0x20), at, 0x1000)
        }
    }
}
