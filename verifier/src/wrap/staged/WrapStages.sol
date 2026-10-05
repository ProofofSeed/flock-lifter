// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "../../Constants.sol";
import {FiatShamir, OutputShape} from "../../FiatShamir.sol";
import {DataStore} from "../../staged/DataStore.sol";
import {F} from "../F.sol";
import {W} from "../W.sol";
import {Whir, WhirClaim, WhirState} from "../Whir.sol";
import {WrapKey} from "../WrapKey.sol";
import {Assist, Opened, WrapOpening} from "../WrapOpening.sol";
import {Run, WrapPiop} from "../WrapPiop.sol";
import {WrapStructure} from "../WrapStructure.sol";
import {Carry, IWrapStage, Stage} from "./Carry.sol";

/// The first stage of a wrapped lift's staged verification: the Fiat-Shamir gate over the published
/// words, the outer proof's statement binding, its zerocheck, its lincheck and its wiring argument.
contract WrapStageA {
    /// The contract holding the fixed public words.
    address public immutable fixedWords;

    error Shape();
    error AssertionWord();

    constructor(address fixedWords_) {
        fixedWords = fixedWords_;
    }

    function start(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata data)
        external
        view
        returns (bytes memory)
    {
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        if (s.counts[0] == 0 || output[s.at[0] + s.counts[0] - 1] != 0x01) revert AssertionWord();
        if (WrapKey.N_IO != 5 + 2 * ((8 * s.payload + 127) / 128)) revert Shape();
        FiatShamir.GateArgs memory g;
        g.outputAt = Stage.at(output);
        g.bindingAt = Stage.at(binding);
        g.bindingLen = binding.length;
        g.n = WrapKey.RESPONSES;
        g.nIo = WrapKey.N_IO;
        g.wordsAt = Stage.at(data);
        g.unopenedAt = g.wordsAt + 16 * WrapKey.N_IO * WrapKey.RESPONSES;
        FiatShamir.gate(s, g);
        Run memory x;
        x.phi = Constants.PHI8;
        x.p = g.unopenedAt + 32 * WrapKey.RESPONSES;
        uint256 child = WrapPiop.bind(x, g.wordsAt, DataStore.read(fixedWords));
        (uint256 a, uint256 b) = WrapPiop.zerocheck(x);
        WrapPiop.lincheck(x, a, b);
        WrapPiop.wiring(x, child);
        W.merge(x.tr, child);
        Carry memory n = Stage.fresh(2, keccak256(abi.encode(keccak256(output), counts, keccak256(binding))));
        n.v[Stage.CURSOR] = x.p - g.wordsAt;
        (n.v[Stage.TR], n.b[Stage.TR_PENDING]) = Stage.saved(x.tr);
        n.v[Stage.ZC_Z] = x.zcZ;
        n.v[Stage.ZC_C] = x.zcC;
        n.v[Stage.LC_VALUE] = x.lcValue;
        n.v[Stage.LIVE] = x.live;
        n.v[Stage.MASKED] = x.masked;
        n.v[Stage.SIGMA] = x.sigma;
        n.a[Stage.MLV] = x.mlv;
        n.a[Stage.R_REST] = x.rRest;
        n.a[Stage.RR] = x.rr;
        n.a[Stage.SKIP] = x.skipAb;
        n.a[Stage.RHO] = x.rho;
        n.b[Stage.Z_PARTIAL] = Stage.slice(x.zPartialAt, 64 * 16);
        n.b[Stage.EVALS] = Stage.slice(x.evalsAt, 32 * WrapKey.N_BOOL);
        n.b[Stage.GATHER] = Stage.slice(x.gatherAt, 16 * WrapKey.N_GATE);
        n.b[Stage.CAP] = Stage.slice(x.capAt, 32 << W.entry(WrapKey.OUTER_ROUNDS, 6, 1));
        // The two accumulated block claims, as the public segment holds them.
        uint256 first = W.entry(WrapKey.ACC, 0, 4);
        uint256 len = 16 * 2 * (2 * WrapKey.K_LOG + 1);
        bytes memory acc = new bytes(len);
        uint256 from = x.pub + 16 * first;
        assembly ("memory-safe") {
            mcopy(add(acc, 0x20), from, len)
        }
        n.b[Stage.ACC] = acc;
        return abi.encode(n);
    }
}

/// What the stages after the first share: the reading of a carried state into working memory.
abstract contract WrapStageBase {
    /// The claims of the interactive proofs that `c` carries, on its outer transcript, with the
    /// cursor at `data`.
    function _load(Carry calldata c, bytes calldata data, uint256 stage) internal pure returns (Run memory x) {
        if (c.stage != stage) revert Stage.WrongStage();
        x.tr = Stage.transcript(c.v[Stage.TR], c.b[Stage.TR_PENDING], 1 << 16);
        x.p = Stage.at(data);
        x.zcZ = c.v[Stage.ZC_Z];
        x.zcC = c.v[Stage.ZC_C];
        x.lcValue = c.v[Stage.LC_VALUE];
        x.live = c.v[Stage.LIVE];
        x.masked = c.v[Stage.MASKED];
        x.sigma = c.v[Stage.SIGMA];
        x.mlv = c.a[Stage.MLV];
        x.rRest = c.a[Stage.R_REST];
        x.rr = c.a[Stage.RR];
        x.rho = c.a[Stage.RHO];
        x.er = c.a[Stage.ER];
        x.ecol = c.a[Stage.ECOL];
        x.zPartialAt = Stage.at(c.b[Stage.Z_PARTIAL]);
        x.evalsAt = Stage.at(c.b[Stage.EVALS]);
        x.gatherAt = Stage.at(c.b[Stage.GATHER]);
        x.capAt = Stage.at(c.b[Stage.CAP]);
    }

    /// Records in `n`, the state after `c`, the cursor moved past what `x` read of `data`, the outer
    /// transcript of `x`, and what every later stage needs of the interactive proofs.
    function _keep(Carry calldata c, bytes calldata data, Run memory x, Carry memory n) internal pure {
        n.v[Stage.CURSOR] = c.v[Stage.CURSOR] + x.p - Stage.at(data);
        (n.v[Stage.TR], n.b[Stage.TR_PENDING]) = Stage.saved(x.tr);
        n.v[Stage.LIVE] = x.live;
        n.v[Stage.MASKED] = x.masked;
        n.v[Stage.SIGMA] = x.sigma;
        n.a[Stage.MLV] = x.mlv;
        n.a[Stage.RR] = x.rr;
        n.a[Stage.RHO] = x.rho;
        n.b[Stage.Z_PARTIAL] = c.b[Stage.Z_PARTIAL];
        n.b[Stage.EVALS] = c.b[Stage.EVALS];
        n.b[Stage.ACC] = c.b[Stage.ACC];
    }

    /// The assist's state that `c` carries.
    function _assist(Carry calldata c) internal pure returns (Assist memory a) {
        a.ch = Stage.transcript(c.v[Stage.CHILD], c.b[Stage.CHILD_PENDING], 1 << 15);
        a.gamma = c.v[Stage.GAMMA];
        a.anchor = c.v[Stage.ANCHOR];
        a.point = c.a[Stage.POINT];
        a.sigma = c.a[Stage.ANCHOR_POINT];
    }

    /// Records in `n` the assist's state, and the committed stack's point and claimed value.
    function _saveAssist(Carry memory n, Assist memory a, uint256[] memory rho, uint256 value) internal pure {
        (n.v[Stage.CHILD], n.b[Stage.CHILD_PENDING]) = Stage.saved(a.ch);
        n.v[Stage.GAMMA] = a.gamma;
        n.v[Stage.ANCHOR] = a.anchor;
        n.v[Stage.VALUE] = value;
        n.a[Stage.POINT] = a.point;
        n.a[Stage.STACK_POINT] = rho;
    }
}

/// The second stage: the element class, the claims' ring switches and batching, the merged
/// sumcheck, the assist's sumchecks and the claims' weights over their square-root chains.
contract WrapStageB is WrapStageBase, IWrapStage {
    /// The contract holding the element tables.
    address public immutable elements;

    error Transport();

    constructor(address elements_) {
        elements = elements_;
    }

    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory) {
        Run memory x = _load(c, data, 2);
        x.phi = Constants.PHI8;
        x.skipAb = c.a[Stage.SKIP];
        WrapPiop.element(x, WrapKey.ELEMS, DataStore.read(elements));
        Carry memory n = Stage.fresh(3, c.digest);
        _transport(x, n);
        _keep(c, data, x, n);
        n.a[Stage.R_REST] = x.rRest;
        n.a[Stage.ER] = x.er;
        n.a[Stage.ECOL] = x.ecol;
        n.a[Stage.SKIP] = x.skipC;
        n.b[Stage.CAP] = c.b[Stage.CAP];
        return abi.encode(n);
    }

    /// The transport of the claims of `x` up to the claims' weights, whose results it records in `n`.
    function _transport(Run memory x, Carry memory n) private pure {
        (Opened memory o, uint256[] memory gammas, uint256[][2] memory r) = WrapOpening.switches(x);
        Assist memory a;
        a.ch = W.fork(x.tr, "flock-par-assist-v1", 1 << 15);
        a.p = x.p;
        WrapOpening.multipoint(a, o.rho.length);
        WrapOpening.anchor(a);
        if (o.target != F.mul(o.value, WrapOpening.rooted(a, gammas, r))) revert Transport();
        x.p = a.p;
        _saveAssist(n, a, o.rho, o.value);
        n.a[Stage.ANCHOR_POINT] = a.sigma;
        n.a[Stage.GAMMAS] = gammas;
    }
}

/// The third stage: the two sums of the layout's last equation, over every claim's layout weight
/// and boundary value.
contract WrapStageC is WrapStageBase, IWrapStage {
    /// The contract holding the layout's runs.
    address public immutable runs;

    constructor(address runs_) {
        runs = runs_;
    }

    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory) {
        Run memory x = _load(c, data, 3);
        Assist memory a = _assist(c);
        WrapOpening.layout(x, a, c.a[Stage.STACK_POINT], c.a[Stage.GAMMAS], DataStore.read(runs), WrapKey.GATE_RUNS);
        Carry memory n = Stage.fresh(4, c.digest);
        _keep(c, data, x, n);
        _saveAssist(n, a, c.a[Stage.STACK_POINT], c.v[Stage.VALUE]);
        n.a[Stage.SKIP] = c.a[Stage.SKIP];
        n.b[Stage.CAP] = c.b[Stage.CAP];
        return abi.encode(n);
    }
}

/// The fourth stage: the outer commitment's opening.
contract WrapStageD is WrapStageBase, IWrapStage {
    /// The contract holding the subspace polynomials' values.
    address public immutable subspace;

    constructor(address subspace_) {
        subspace = subspace_;
    }

    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory) {
        Run memory x = _load(c, data, 4);
        Assist memory a = _assist(c);
        uint256[] memory rho = c.a[Stage.STACK_POINT];
        WhirClaim memory w;
        w.rounds = WrapKey.OUTER_ROUNDS;
        w.finalVars = WrapKey.OUTER_FINAL;
        w.powBits = WrapKey.OUTER_POW;
        bytes memory cap = c.b[Stage.CAP];
        w.cap = W.data(cap);
        w.points = new uint256[][](1);
        w.points[0] = rho;
        w.values = new uint256[](1);
        w.values[0] = c.v[Stage.VALUE];
        W.append(x.tr, WrapKey.OUTER_START);
        W.append(x.tr, cap);
        bytes memory space = DataStore.read(subspace);
        WhirState memory st = Whir.open(x.tr, w, x.p, space);
        x.p = st.p;
        Whir.weigh(st, w.rounds, space);
        W.merge(x.tr, a.ch);
        Carry memory n = Stage.fresh(5, c.digest);
        _keep(c, data, x, n);
        n.a[Stage.SKIP] = c.a[Stage.SKIP];
        return abi.encode(n);
    }
}

/// The fifth stage: the proof of the committed tables down to its one claim on the committed
/// bytes' bits.
contract WrapStageE is WrapStageBase, IWrapStage {
    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory) {
        Run memory x = _load(c, data, 5);
        x.skipC = c.a[Stage.SKIP];
        // The public segment is carried from its first accumulated claim on.
        bytes memory acc = c.b[Stage.ACC];
        unchecked {
            x.pub = W.data(acc) - 16 * W.entry(WrapKey.ACC, 0, 4);
        }
        uint256[] memory claimed = new uint256[](2);
        uint256[] memory point;
        (point, claimed[0], claimed[1]) = WrapStructure.reduce(x);
        Carry memory n = Stage.fresh(6, c.digest);
        n.v[Stage.CURSOR] = c.v[Stage.CURSOR] + x.p - Stage.at(data);
        (n.v[Stage.TR], n.b[Stage.TR_PENDING]) = Stage.saved(x.tr);
        n.a[Stage.CLAIMS] = point;
        n.a[Stage.CLAIMED] = claimed;
        return abi.encode(n);
    }
}

/// The sixth stage: the committed bytes' values at the conjugates of the bit claim's point, and
/// the tables' commitment's opening up to its last equation.
contract WrapStageF is IWrapStage {
    /// The contract holding the subspace polynomials' values.
    address public immutable subspace;

    constructor(address subspace_) {
        subspace = subspace_;
    }

    function run(Carry calldata c, bytes calldata data) external view returns (bytes memory) {
        if (c.stage != 6) revert Stage.WrongStage();
        uint256 tr = Stage.transcript(c.v[Stage.TR], c.b[Stage.TR_PENDING], 1 << 17);
        uint256[] memory claimed = c.a[Stage.CLAIMED];
        WhirClaim memory w;
        uint256 p;
        (w.points, w.values, p) = WrapStructure.conjugates(c.a[Stage.CLAIMS], claimed[0], claimed[1], Stage.at(data));
        w.rounds = WrapKey.STRUCT_ROUNDS;
        w.finalVars = WrapKey.STRUCT_FINAL;
        w.powBits = WrapKey.STRUCT_POW;
        w.cap = W.data(WrapKey.STRUCT_CAP);
        W.append(tr, WrapKey.STRUCT_START);
        WhirState memory st = Whir.open(tr, w, p, DataStore.read(subspace));
        Carry memory n = Stage.fresh(7, c.digest);
        n.v[Stage.CURSOR] = c.v[Stage.CURSOR] + st.p - Stage.at(data);
        Stage.saveWhir(n, st, W.read(w.rounds, 5, 1), w.points.length, WrapKey.STRUCT_N);
        return abi.encode(n);
    }
}

/// The seventh stage: the tables' opening's last equation, which ends the verification.
contract WrapStageG is IWrapStage {
    /// The contract holding the subspace polynomials' values.
    address public immutable subspace;

    constructor(address subspace_) {
        subspace = subspace_;
    }

    function run(Carry calldata c, bytes calldata) external view returns (bytes memory) {
        if (c.stage != 7) revert Stage.WrongStage();
        uint256 points = c.b[Stage.WHIR_POINTS].length / (16 * WrapKey.STRUCT_N);
        Whir.weigh(Stage.loadWhir(c, WrapKey.STRUCT_ROUNDS, points), WrapKey.STRUCT_ROUNDS, DataStore.read(subspace));
        Carry memory n = Stage.fresh(Stage.DONE, c.digest);
        n.v[Stage.CURSOR] = c.v[Stage.CURSOR];
        return abi.encode(n);
    }
}
