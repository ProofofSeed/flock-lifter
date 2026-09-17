// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {GF2} from "../GF2.sol";
import {Residual} from "../Residual.sol";
import {DataStore} from "./DataStore.sol";
import {IStage, Staged, State} from "./Staged.sol";
import {Walk} from "./Walk.sol";

/// The consistency residual stage of a batched opening: each level's consistency basis in items,
/// its prefix factors and its suffix form, then the opening's final check.
contract ConsistencyStages is IStage {
    /// The contract holding `Constants.SUBSPACE`.
    address public immutable subspace;

    error Shape();

    constructor(address subspace_) {
        subspace = subspace_;
    }

    function run(bytes calldata state, uint256 upto, bytes calldata)
        external
        view
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.CONS, Staged.CONS);
        if (upto <= st.v[Staged.CURSOR] || upto > st.v[Staged.ITEMS]) revert Shape();
        _cons(st, upto);
        return (Staged.save(st), Staged.request(st, new uint256[](0)));
    }

    function _cons(State memory st, uint256 upto) private view {
        bytes memory table = DataStore.read(subspace);
        uint256 item = st.v[Staged.CURSOR];
        uint256 level;
        uint256 j = item;
        uint256[] memory fixedPart = Walk.originalChallenges(st, st.a[Staged.CONS_START][0], false);
        while (j >= fixedPart.length + 1) {
            j -= fixedPart.length + 1;
            ++level;
            fixedPart = Walk.originalChallenges(st, st.a[Staged.CONS_START][level], false);
        }
        while (item < upto) {
            uint256 did = _consLevel(st, level, j, upto - item, fixedPart, table);
            item += did;
            j += did;
            if (j == fixedPart.length + 1 && item < st.v[Staged.ITEMS]) {
                ++level;
                j = 0;
                fixedPart = Walk.originalChallenges(st, st.a[Staged.CONS_START][level], false);
            }
        }
        st.v[Staged.CURSOR] = upto;
        if (upto < st.v[Staged.ITEMS]) return;
        st.a[Staged.WORK] = new uint256[](0);
        Staged.enter(st, st.v[Staged.KIND] == 1 ? Staged.CHECK : Staged.M_CHECK, 1);
    }

    /// Runs up to `budget` items of consistency level `level` from its item `j`, returning how many
    /// it ran.
    function _consLevel(
        State memory st,
        uint256 level,
        uint256 j,
        uint256 budget,
        uint256[] memory fixedPart,
        bytes memory table
    )
        private
        pure
        returns (uint256 did)
    {
        uint256[] memory qs = st.a[Staged.CONS_Q + level];
        uint256[] memory mu = st.a[Staged.MU];
        uint256[] memory ctx = Residual.context(st.a[Staged.CONS_COLS][level], qs, fixedPart.length, mu.length, table);
        if (j == 0) {
            uint256[] memory weights = GF2.eqTable(st.a[Staged.CONS_ALPHA + level]);
            uint256[] memory p = new uint256[](qs.length);
            for (uint256 i = 0; i < qs.length; ++i) {
                p[i] = weights[i];
            }
            st.a[Staged.WORK] = p;
        }
        uint256[] memory work = st.a[Staged.WORK];
        while (did < budget && j < fixedPart.length) {
            Residual.factor(ctx, qs, work, j, fixedPart[j]);
            ++j;
            ++did;
        }
        if (did < budget && j == fixedPart.length) {
            uint256 value = Residual.collect(ctx, qs, work, mu);
            uint256 scale = GF2.mul256By128(
                Walk.factorProduct(st, st.a[Staged.CONS_START][level]), st.a[Staged.CONS_BETA][level]
            );
            st.v[Staged.GOT] ^= GF2.mul256(value, scale);
            ++did;
        }
    }
}
