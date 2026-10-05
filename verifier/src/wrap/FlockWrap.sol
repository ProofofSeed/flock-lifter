// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "../Constants.sol";
import {F} from "./F.sol";
import {FiatShamir, OutputShape} from "../FiatShamir.sol";
import {Whir, WhirClaim, WhirState} from "./Whir.sol";
import {Assist, Opened, WrapOpening} from "./WrapOpening.sol";
import {Run, WrapPiop} from "./WrapPiop.sol";
import {WrapStructure} from "./WrapStructure.sol";
import {Transcript} from "../Transcript.sol";
import {W} from "./W.sol";
import {WrapKey} from "./WrapKey.sol";

/// The verifier of a wrapped lift of a hardened-child proof of seed, for one statement circuit and
/// one lift shape: the wrap's outer proof, the proof of what it leaves about the committed tables,
/// and the global Fiat-Shamir gate over the published words.
contract FlockWrap {
    error Shape();
    error AssertionWord();
    error Transport();

    /// Verifies a wrapped lift against the expected output `output`, which ZKBoo serialised from
    /// `counts & 0xffff` 8-bit, `(counts >> 16) & 0xffff` 32-bit and `counts >> 32` 64-bit words,
    /// under `binding`; returns the transcript's last state.
    function verify(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata lift)
        external
        returns (bytes32)
    {
        return _run(output, counts, binding, lift, type(uint256).max);
    }

    function _run(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata lift, uint256 stop)
        internal
        returns (bytes32)
    {
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        if (s.counts[0] == 0 || output[s.at[0] + s.counts[0] - 1] != 0x01) revert AssertionWord();
        if (WrapKey.N_IO != 5 + 2 * ((8 * s.payload + 127) / 128)) revert Shape();
        FiatShamir.GateArgs memory g;
        g.outputAt = _offset(output);
        g.bindingAt = _offset(binding);
        g.bindingLen = binding.length;
        g.n = WrapKey.RESPONSES;
        g.nIo = WrapKey.N_IO;
        g.wordsAt = _offset(lift);
        g.unopenedAt = g.wordsAt + 16 * WrapKey.N_IO * WrapKey.RESPONSES;
        Run memory x;
        x.phi = Constants.PHI8;
        x.p = g.unopenedAt + 32 * WrapKey.RESPONSES;
        uint256 free = W.top();
        FiatShamir.gate(s, g);
        W.release(free);
        if (!_proofs(x, g.wordsAt, stop)) return bytes32(0);
        if (x.p != g.wordsAt + lift.length) revert Shape();
        return W.state(x.tr);
    }

    /// Verifies the proofs at the cursor; returns whether it ran to the end rather than to `stop`.
    function _proofs(Run memory x, uint256 wordsAt, uint256 stop) private returns (bool) {
        uint256 child = WrapPiop.bind(x, wordsAt, WrapKey.FIXED);
        W.mark(1, x.tr);
        if (stop == 1) return false;
        (uint256 a, uint256 b) = WrapPiop.zerocheck(x);
        W.mark(2, x.tr);
        if (stop == 2) return false;
        WrapPiop.lincheck(x, a, b);
        W.mark(3, x.tr);
        if (stop == 3) return false;
        WrapPiop.wiring(x, child);
        W.mark(4, child);
        if (stop == 4) return false;
        W.merge(x.tr, child);
        WrapPiop.element(x, WrapKey.ELEMS, WrapKey.ELEM_DATA);
        W.mark(5, x.tr);
        if (stop == 5) return false;
        child = _transport(x, stop);
        if (child == 0) return false;
        W.merge(x.tr, child);
        W.mark(10, x.tr);
        if (stop == 10) return false;
        _structure(x);
        W.mark(20, x.tr);
        return stop != 20;
    }

    /// The transport of the outer proof's claims and the outer commitment's opening; returns the
    /// assist's transcript, or zero if it stopped at `stop`.
    function _transport(Run memory x, uint256 stop) private returns (uint256) {
        (Opened memory o, uint256[] memory gammas, uint256[][2] memory r) = WrapOpening.switches(x);
        W.mark(6, x.tr);
        if (stop == 6) return 0;
        Assist memory a;
        a.ch = W.fork(x.tr, "flock-par-assist-v1", 1 << 15);
        a.p = x.p;
        WrapOpening.multipoint(a, o.rho.length);
        W.mark(7, a.ch);
        if (stop == 7) return 0;
        WrapOpening.anchor(a);
        W.mark(8, a.ch);
        if (stop == 8) return 0;
        o.weight = WrapOpening.rooted(a, gammas, r);
        if (o.target != F.mul(o.value, o.weight)) revert Transport();
        W.mark(81, a.ch);
        uint256 free = W.top();
        WrapOpening.layout(x, a, o.rho, gammas, WrapKey.RUNS, WrapKey.GATE_RUNS);
        W.release(free);
        W.mark(82, a.ch);
        x.p = a.p;
        WhirClaim memory c;
        c.rounds = WrapKey.OUTER_ROUNDS;
        c.finalVars = WrapKey.OUTER_FINAL;
        c.powBits = WrapKey.OUTER_POW;
        uint256 len = 32 << W.entry(c.rounds, 6, 1);
        uint256 cap;
        uint256 capAt = x.capAt;
        assembly ("memory-safe") {
            cap := mload(0x40)
            mstore(0x40, add(cap, len))
            calldatacopy(cap, capAt, len)
        }
        c.cap = cap;
        c.points = new uint256[][](1);
        c.points[0] = o.rho;
        c.values = new uint256[](1);
        c.values[0] = o.value;
        W.append(x.tr, WrapKey.OUTER_START);
        W.appendCalldata(x.tr, capAt, len);
        bytes memory space = WrapKey.SUBSPACE;
        WhirState memory st = Whir.open(x.tr, c, x.p, space);
        x.p = st.p;
        W.mark(9, x.tr);
        if (stop == 9) return 0;
        Whir.weigh(st, c.rounds, space);
        W.release(free);
        W.mark(91, x.tr);
        return a.ch;
    }

    /// The proof of what the outer proof leaves about the committed tables.
    function _structure(Run memory x) private {
        (uint256[] memory point, uint256 claim, uint256 weight) = WrapStructure.reduce(x);
        W.mark(11, x.tr);
        WhirClaim memory c;
        (c.points, c.values, x.p) = WrapStructure.conjugates(point, claim, weight, x.p);
        W.mark(12, x.tr);
        c.rounds = WrapKey.STRUCT_ROUNDS;
        c.finalVars = WrapKey.STRUCT_FINAL;
        c.powBits = WrapKey.STRUCT_POW;
        c.cap = W.data(WrapKey.STRUCT_CAP);
        W.append(x.tr, WrapKey.STRUCT_START);
        bytes memory space = WrapKey.SUBSPACE;
        WhirState memory st = Whir.open(x.tr, c, x.p, space);
        x.p = st.p;
        W.mark(13, x.tr);
        Whir.weigh(st, c.rounds, space);
    }

    function _offset(bytes calldata b) private pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }
}
