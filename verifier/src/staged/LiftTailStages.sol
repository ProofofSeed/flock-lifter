// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "../Constants.sol";
import {FiatShamir, OutputShape} from "../FiatShamir.sol";
import {GF2} from "../GF2.sol";
import {Piop} from "../Piop.sol";
import {LiftLayout} from "./LiftStages.sol";
import {IStage, Staged, State} from "./Staged.sol";

/// The lift's last stages: each chunk's published-word claim in row ranges and its final check,
/// and the global Fiat-Shamir gate.
contract LiftTailStages is IStage {
    error Shape();
    error Words();
    error Final();

    function run(bytes calldata state, uint256 upto, bytes calldata data)
        external
        pure
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.IO, Staged.GATE);
        uint256 stage = st.v[Staged.STAGE];
        uint256[] memory streams;
        if (stage == Staged.IO) {
            streams = _io(st, upto, data);
        } else if (stage == Staged.CHECK) {
            streams = _check(st);
        } else {
            return _gate(st, data);
        }
        return (Staged.save(st), Staged.request(st, streams));
    }

    /// The published-word claim's tables: the word map, the word weights and the row weights.
    struct IoTables {
        uint256[] table;
        uint256[] eWord;
        uint256[] eRow;
    }

    function _ioTables(State memory st) private pure returns (IoTables memory t) {
        uint256[] memory io = st.a[Staged.ACCS];
        uint256[] memory rWord = new uint256[](4);
        uint256[] memory xOuter = new uint256[](st.v[Staged.NU]);
        for (uint256 k = 0; k < 4; ++k) {
            rWord[k] = io[2 + k];
        }
        for (uint256 k = 0; k < xOuter.length; ++k) {
            xOuter[k] = io[6 + k];
        }
        t.table = Piop.linearTable(Piop.lagrange(Constants.PHI8, io[0]), io[1]);
        t.eWord = GF2.eqTable(rWord);
        t.eRow = GF2.eqTable(xOuter);
    }

    function _io(State memory st, uint256 upto, bytes calldata data) private pure returns (uint256[] memory) {
        uint256 cursor = st.v[Staged.CURSOR];
        uint256 live = st.v[Staged.LIVE];
        uint256 nIo = st.v[Staged.NIO];
        if (upto <= cursor || upto > live || data.length != 16 * nIo * (upto - cursor)) revert Shape();
        IoTables memory t = _ioTables(st);
        uint256 at = Staged.offset(data);
        for (uint256 j = cursor; j < upto; ++j) {
            uint256 acc = Piop.rowValue(t.table, t.eWord, at + 16 * nIo * (j - cursor), nIo);
            if (j + 1 == live) {
                st.v[Staged.IO_LAST] = acc;
            } else {
                st.v[Staged.IO_VALUE] ^= GF2.mul(t.eRow[j], acc);
            }
        }
        st.v[Staged.CURSOR] = upto;
        if (upto < live) {
            return LiftLayout.rowStreams(st);
        }
        uint256 tail;
        for (uint256 j = live - 1; j < t.eRow.length; ++j) {
            tail ^= t.eRow[j];
        }
        st.a[Staged.CL_VALUE][2] = st.v[Staged.IO_VALUE] ^ GF2.mul(tail, st.v[Staged.IO_LAST]);
        st.a[Staged.ACCS] = new uint256[](0);
        Staged.enter(st, Staged.SWITCH, 1);
        return Staged.sequential(st.v[Staged.POS]);
    }

    function _check(State memory st) private pure returns (uint256[] memory) {
        if (st.v[Staged.GOT] != st.v[Staged.CLAIM] || st.v[Staged.POS] != st.v[Staged.CHUNK_END]) revert Final();
        uint256[] memory packed = st.a[Staged.PACKED];
        uint256[] memory mc = st.a[Staged.MC];
        uint256[] memory next = new uint256[](packed.length + mc.length);
        for (uint256 k = 0; k < packed.length; ++k) {
            next[k] = packed[k];
        }
        for (uint256 k = 0; k < mc.length; ++k) {
            next[packed.length + k] = mc[k];
        }
        State memory clean = Staged.fresh(1);
        uint256[] memory keep = new uint256[](13);
        keep[0] = Staged.N;
        keep[1] = Staged.CHUNK;
        keep[2] = Staged.NIO;
        keep[3] = Staged.NCHUNKS;
        keep[4] = Staged.SLIM;
        keep[5] = Staged.WORDS_AT;
        keep[6] = Staged.UNOPENED_AT;
        keep[7] = Staged.DIGEST;
        keep[8] = Staged.STATEMENT;
        keep[9] = Staged.OUTPUT_LEN;
        keep[10] = Staged.BINDING_LEN;
        keep[11] = Staged.COUNTS;
        keep[12] = Staged.POS;
        for (uint256 k = 0; k < keep.length; ++k) {
            clean.v[keep[k]] = st.v[keep[k]];
        }
        clean.a[Staged.WORD_HASHES] = st.a[Staged.WORD_HASHES];
        clean.a[Staged.PACKED] = next;
        clean.v[Staged.CHUNK_I] = st.v[Staged.CHUNK_I] + 1;
        st.v = clean.v;
        st.a = clean.a;
        st.tr = "";
        if (st.v[Staged.CHUNK_I] < st.v[Staged.NCHUNKS]) {
            return LiftLayout.enterHead(st);
        }
        Staged.enter(st, Staged.GATE, 1);
        return Staged.want2(
            Staged.want2(
                Staged.want1(Staged.OUTPUT, 0, 0, st.v[Staged.OUTPUT_LEN]),
                Staged.want1(Staged.BINDING, 0, 0, st.v[Staged.BINDING_LEN])
            ),
            LiftLayout.region(st)
        );
    }

    /// Runs the gate over the output, the binding and the published region, and ends the lift
    /// with its statement digest and the hash of its packed matrix claims.
    function _gate(State memory st, bytes calldata data) private pure returns (bytes memory, uint256[] memory) {
        uint256 outLen = st.v[Staged.OUTPUT_LEN];
        uint256 bindLen = st.v[Staged.BINDING_LEN];
        uint256 regionLen = st.v[Staged.UNOPENED_AT] + 32 * st.v[Staged.N];
        if (data.length != outLen + bindLen + regionLen) revert Shape();
        if (uint256(keccak256(abi.encodePacked(data[:outLen + bindLen], st.v[Staged.COUNTS]))) != st.v[Staged.STATEMENT]) {
            revert Shape();
        }
        uint256 regionAt = Staged.offset(data) + outLen + bindLen;
        if (uint256(Staged.hashAt(regionAt, regionLen)) != st.a[Staged.WORD_HASHES][st.v[Staged.NCHUNKS]]) {
            revert Words();
        }
        _runGate(st, data[:outLen], Staged.offset(data) + outLen, regionAt);
        bytes memory done = abi.encodePacked(
            bytes32(Staged.LIFT_DONE), bytes32(st.v[Staged.DIGEST]), keccak256(abi.encodePacked(st.a[Staged.PACKED]))
        );
        return (done, new uint256[](0));
    }

    function _runGate(State memory st, bytes calldata output, uint256 bindingAt, uint256 regionAt) private pure {
        uint256 counts = st.v[Staged.COUNTS];
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        FiatShamir.GateArgs memory g;
        g.outputAt = Staged.offset(output);
        g.bindingAt = bindingAt;
        g.bindingLen = st.v[Staged.BINDING_LEN];
        g.n = st.v[Staged.N];
        g.nIo = st.v[Staged.NIO];
        g.wordsAt = regionAt + st.v[Staged.WORDS_AT];
        g.unopenedAt = regionAt + st.v[Staged.UNOPENED_AT];
        FiatShamir.gate(s, g);
    }

}
