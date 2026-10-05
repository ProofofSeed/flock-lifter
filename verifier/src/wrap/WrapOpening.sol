// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
import {K} from "./K.sol";
import {W} from "./W.sol";
import {WrapKey} from "./WrapKey.sol";
import {Run} from "./WrapPiop.sol";

/// What the transport of a wrap's claims leaves: the point of the committed stack, its claimed
/// value there, and the two sides of the transport's last equation.
struct Opened {
    uint256[] rho;
    uint256 value;
    uint256 target;
    uint256 weight;
}

/// One ring-switched claim: its point, its point's equality table, and its switched sum.
struct Switched {
    uint256[] r;
    uint256[] eq;
    uint256 sum;
}

/// The assist's state: its transcript and cursor, the batching challenge of the dual values with
/// where they sit in calldata, the multipoint sumcheck's point and last claim, and the anchor's
/// point, claimed value and last claim.
struct Assist {
    uint256 ch;
    uint256 p;
    uint256 gamma;
    uint256 valuesAt;
    uint256[] point;
    uint256[] sigma;
    uint256 claim;
    uint256 anchor;
    uint256 v;
}

/// The opening of a wrap's outer proof up to its commitment: Flock's merged transport of the
/// claims onto one evaluation of the committed stack, with the linearised coefficients, the
/// twisted equality and the layout's weights in closed form.
library WrapOpening {
    error RingSwitchClaim();
    error RowPoints();
    error Layout();
    error Multipoint();
    error Roots();

    // "flock-merged-open-v1"
    uint256 internal constant L_MERGED_0 = 0x02000000000000000000000000000014666c6f636b2d6d65726765642d6f7065;
    uint256 internal constant L_MERGED_1 = 0x6e2d763100000000000000000000000000000000000000000000000000000000;
    // "flock-ring-switch-v0"
    uint256 internal constant L_RING_0 = 0x02000000000000000000000000000014666c6f636b2d72696e672d7377697463;
    uint256 internal constant L_RING_1 = 0x682d763000000000000000000000000000000000000000000000000000000000;
    // "flock-multipoint-twisted-v1"
    uint256 internal constant L_MULTI_0 = 0x0200000000000000000000000000001b666c6f636b2d6d756c7469706f696e74;
    uint256 internal constant L_MULTI_1 = 0x2d747769737465642d7631000000000000000000000000000000000000000000;
    // "flock-frobenius-assist-v0"
    uint256 internal constant L_FROB_0 = 0x02000000000000000000000000000019666c6f636b2d66726f62656e6975732d;
    uint256 internal constant L_FROB_1 = 0x6173736973742d76300000000000000000000000000000000000000000000000;

    /// The nibble tables of `e ↦ Σ_j bit_j(e)·coeffs[j]`: entry `16·k + n` is the image of nibble
    /// `n` at nibble position `k`.
    function bitTable(uint256[] memory coeffs) internal pure returns (uint256[] memory t) {
        t = new uint256[](32 * 16);
        for (uint256 k = 0; k < 32; ++k) {
            uint256 base = 16 * k;
            for (uint256 n = 1; n < 16; ++n) {
                uint256 low = n & (~n + 1);
                uint256 bit = low == 1 ? 0 : low == 2 ? 1 : low == 4 ? 2 : 3;
                t[base + n] = t[base + (n ^ low)] ^ coeffs[4 * k + bit];
            }
        }
    }

    function applyTable(uint256[] memory t, uint256 word) internal pure returns (uint256 acc) {
        assembly ("memory-safe") {
            let base := add(t, 0x20)
            for { let k := 0 } lt(k, 32) { k := add(k, 1) } {
                let n := and(shr(mul(k, 4), word), 15)
                acc := xor(acc, mload(add(base, shl(5, add(mul(k, 16), n)))))
            }
        }
    }

    /// One claim's ring switch: checks the claim against the sliced message at `p`, and returns
    /// the sampled point, its equality table and the switched sum.
    function ringSwitch(uint256 tr, uint256[] memory skip, uint256 x0, uint256 value, uint256 p)
        internal
        pure
        returns (Switched memory s)
    {
        Transcript.label(tr, L_RING_0, L_RING_1, 48);
        Transcript.observeSliceFromCalldata(tr, p, 128);
        if (K.sliceCheck(W.ptr(skip), x0, p) != value) revert RingSwitchClaim();
        s.r = Transcript.powSampleVec(tr, Calldata.nonce(p + 128 * 16), 3, 7);
        s.eq = W.eqTable(s.r, 0, 7, 1);
        uint256[] memory table = bitTable(s.eq);
        uint256 sum;
        for (uint256 i = 128; i > 0; --i) {
            uint256 l = applyTable(table, Calldata.f128(p + 16 * (i - 1)));
            sum = ((sum << 1) & W.M128) ^ ((sum >> 127) * 0x87) ^ l;
        }
        s.sum = sum;
    }

    /// `Σ_j gamma^j·eq(rho^(2^-j), x)` over the 128 inverse Frobenius powers of `rho`, as the
    /// square of a chain of squarings over `Π_i (1 + rho_i + x_i^(2^j))`.
    function twistedEq(uint256 gamma, uint256[] memory rho, uint256[] memory x) internal pure returns (uint256) {
        uint256 n = rho.length;
        uint256[] memory powers = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            powers[i] = x[i];
        }
        return K.twistedEq(gamma, W.ptr(rho), W.ptr(powers), n);
    }

    function _differ(uint256[] memory a, uint256 ai, uint256[] memory b, uint256 bi, uint256 n) private pure returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            if (a[ai + i] != b[bi + i]) return true;
        }
        return false;
    }

    /// The transport's first part: both ring switches, the batching of every claim, and the merged
    /// sumcheck down to the committed stack's point. Returns the batching coefficients and the two
    /// ring-switched points.
    function switches(Run memory x) internal pure returns (Opened memory o, uint256[] memory gammas, uint256[][2] memory r) {
        uint256 tr = x.tr;
        uint256 p = x.p;
        Transcript.label(tr, L_MERGED_0, L_MERGED_1, 48);
        Switched[2] memory sw;
        sw[0] = ringSwitch(tr, x.skipAb, x.rr[0], x.lcValue, p);
        p += 128 * 16 + 8;
        x.skipC = W.lagrange(x.phi, x.zcZ);
        sw[1] = ringSwitch(tr, x.skipC, x.rRest[0], x.zcC, p);
        p += 128 * 16 + 8;
        r[0] = sw[0].r;
        r[1] = sw[1].r;
        Transcript.observe(tr, x.ec);
        Transcript.observe(tr, x.zEval);
        for (uint256 i = 0; i < WrapKey.N_GATE; ++i) {
            Transcript.observe(tr, Calldata.f128(x.gatherAt + 16 * i));
        }
        gammas = Transcript.powSampleVec(tr, Calldata.nonce(p), 6, 4 + WrapKey.N_GATE);
        p += 8;
        uint256 running = F.mul(gammas[0], sw[0].sum) ^ F.mul(gammas[1], sw[1].sum) ^ F.mul(gammas[2], x.ec) ^ F.mul(gammas[3], x.zEval);
        running ^= K.dotCalldata(W.ptr(gammas) + 4 * 32, x.gatherAt, WrapKey.N_GATE);
        o.rho = new uint256[](WrapKey.DENSE_LOG);
        for (uint256 i = 0; i < WrapKey.DENSE_LOG; ++i) {
            uint256 g1 = Calldata.f128(p);
            uint256 ginf = Calldata.f128(p + 16);
            Transcript.observe(tr, g1);
            Transcript.observe(tr, ginf);
            uint256 c = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            running = W.quadratic(running, g1, ginf, c);
            o.rho[i] = c;
        }
        o.value = Calldata.f128(p);
        o.target = running;
        x.p = p + 16;
        // The statements' rows must differ: Flock merges equal ones, which this verifier does not.
        uint256 nu = WrapKey.NU;
        if (
            !_differ(x.mlv, 1, x.rRest, 1, nu) || !_differ(x.mlv, 1, x.er, 0, nu) || !_differ(x.mlv, 1, x.rho, 0, nu)
                || !_differ(x.rRest, 1, x.er, 0, nu) || !_differ(x.rRest, 1, x.rho, 0, nu) || !_differ(x.er, 0, x.rho, 0, nu)
        ) revert RowPoints();
    }

    /// The multipoint reduction of the dual values on the assist's transcript: their batching and
    /// its sumcheck.
    function multipoint(Assist memory a, uint256 m) internal pure {
        uint256 ch = a.ch;
        uint256 p = a.p;
        Transcript.label(ch, L_MULTI_0, L_MULTI_1, 48);
        a.valuesAt = p;
        for (uint256 i = 0; i < 258; ++i) {
            Transcript.observe(ch, Calldata.f128(p + 16 * i));
        }
        p += 258 * 16;
        a.gamma = Transcript.powSample(ch, Calldata.nonce(p), 9);
        p += 8;
        uint256 claim = K.horner(a.valuesAt, 258, a.gamma);
        a.point = new uint256[](m);
        for (uint256 i = 0; i < m; ++i) {
            uint256 g1 = Calldata.f128(p);
            uint256 ginf = Calldata.f128(p + 16);
            Transcript.observe(ch, g1);
            Transcript.observe(ch, ginf);
            uint256 r = Transcript.powSample(ch, Calldata.nonce(p + 32), 2);
            p += 40;
            claim = W.quadratic(claim, g1, ginf, r);
            a.point[i] = r;
        }
        a.claim = claim;
        a.p = p;
    }

    /// The anchor's sumcheck over the boundary bits, and the multipoint sumcheck's last equation.
    function anchor(Assist memory a) internal pure {
        uint256 ch = a.ch;
        uint256 p = a.p;
        uint256 n = 2 * (a.point.length + 1);
        Transcript.label(ch, L_FROB_0, L_FROB_1, 48);
        a.v = Calldata.f128(p);
        Transcript.observe(ch, a.v);
        p += 16;
        uint256 claim = a.v;
        a.sigma = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            uint256 g1 = Calldata.f128(p);
            uint256 ginf = Calldata.f128(p + 16);
            Transcript.observe(ch, g1);
            Transcript.observe(ch, ginf);
            uint256 r = Transcript.powSample(ch, Calldata.nonce(p + 32), 2);
            p += 40;
            claim = W.quadratic(claim, g1, ginf, r);
            a.sigma[i] = r;
        }
        a.anchor = claim;
        a.p = p;
        if (a.claim != a.v) revert Multipoint();
    }

    /// The claims' weights at the committed stack's point, as the assist proves them: the two
    /// ring-switched claims' sums over the square-root chains at the cursor, and the two groups'
    /// values.
    function rooted(Assist memory a, uint256[] memory gammas, uint256[][2] memory r) internal pure returns (uint256 weight) {
        weight = Calldata.f128(a.valuesAt + 256 * 16) ^ Calldata.f128(a.valuesAt + 257 * 16);
        for (uint256 i = 0; i < 2; ++i) {
            (uint256 sum, bool ok) = K.rootedSum(gammas[i], W.ptr(r[i]), a.p, a.valuesAt + 128 * 16 * i, WrapKey.D0);
            if (!ok) revert Roots();
            weight ^= sum;
            a.p += 127 * 128;
        }
    }

    /// `eq(bits(t0), sigma's even coordinates)·eq(bits(t1), sigma's odd coordinates)` per run.
    function _atRuns(uint256[] memory sigma, bytes memory runs) private pure returns (uint256[] memory at) {
        uint256 layers = sigma.length / 2;
        uint256[] memory even = new uint256[](layers);
        uint256[] memory odd = new uint256[](layers);
        for (uint256 l = 0; l < layers; ++l) {
            even[l] = sigma[2 * l];
            odd[l] = sigma[2 * l + 1];
        }
        uint256[] memory tables = new uint256[](6);
        for (uint256 c = 0; c < 3; ++c) {
            uint256 n = layers - 8 * c < 8 ? layers - 8 * c : 8;
            tables[c] = W.ptr(W.eqTable(even, 8 * c, n, 1));
            tables[3 + c] = W.ptr(W.eqTable(odd, 8 * c, n, 1));
        }
        uint256 count = runs.length / 12;
        at = new uint256[](count);
        K.atRuns(W.ptr(at), W.data(runs), count, W.ptr(tables));
    }

    /// `Σ_runs at[run]·Σ_{columns of the run} table[column − base]`, the table taken as zero
    /// outside `[base, base + table.length)`.
    function _weigh(uint256[] memory table, uint256 base, bytes memory runs, uint256[] memory at) private pure returns (uint256) {
        return K.weigh(W.ptr(table), base, table.length, W.data(runs), at.length, W.ptr(at));
    }

    /// The branching program's value over the boundary bits at `sigma`, for the row point
    /// `row[from .. from + NU)` and the dense index `index`.
    function _boundary(uint256[] memory row, uint256 from, uint256[] memory index, uint256[] memory sigma) private pure returns (uint256) {
        return K.boundary(W.ptr(row) + 32 * from, WrapKey.NU, W.ptr(index), index.length, W.ptr(sigma), sigma.length / 2);
    }

    /// The two sums of the anchor's last equation: over the claims on the committed bits, each
    /// statement's batching power, layout weight and boundary value at the anchor's point, and the
    /// same over the claims on the committed words. `runs` and `gateRuns` are the layout's tables.
    function layoutSums(Run memory x, Assist memory a, uint256[] memory gammas, bytes memory runs, bytes memory gateRuns)
        internal
        pure
        returns (uint256 bits, uint256 words)
    {
        uint256[] memory at = _atRuns(a.sigma, runs);
        uint256 nu = WrapKey.NU;
        uint256 low = WrapKey.M_BOOL - nu - 7;
        uint256 g128 = K.frob(a.gamma, 7);
        uint256 g256 = F.sq(g128);
        // The two claims on the committed bits: their column points end in zeros.
        bits = F.mul(_weigh(W.eqTable(x.rr, 1, low, 1), 0, runs, at), _boundary(x.mlv, 1, a.point, a.sigma))
            ^ F.mul(g128, F.mul(_weigh(W.eqTable(x.rRest, 1 + nu, low, 1), 0, runs, at), _boundary(x.rRest, 1, a.point, a.sigma)));
        // The element class's two claims share their rows; their column points end in the region's frozen bits.
        {
            uint256 cols = x.ecol.length;
            uint256 base = WrapKey.ELEM_FROZEN << cols;
            uint256 w = _weigh(W.eqTable(x.er, nu, cols, gammas[2]), base, runs, at) ^ _weigh(W.eqTable(x.ecol, 0, cols, gammas[3]), base, runs, at);
            words = F.mul(g256, F.mul(w, _boundary(x.er, 0, a.point, a.sigma)));
        }
        // The gathered cell slots share the wiring point's rows; each reads one column.
        {
            uint256[] memory hot = new uint256[](at.length);
            for (uint256 i = 0; i < WrapKey.N_GATE; ++i) {
                hot[W.entry(gateRuns, i, 2)] ^= gammas[4 + i];
            }
            uint256 w = K.dot(W.ptr(hot), W.ptr(at), at.length);
            words ^= F.mul(F.mul(g256, a.gamma), F.mul(w, _boundary(x.rho, 0, a.point, a.sigma)));
        }
    }

    /// Checks the anchor's last equation from its two sums: the claims on the bits weigh the
    /// twisted equality of the stack's point `rho` at the multipoint sumcheck's point, and the
    /// claims on the words the plain one.
    function layoutCheck(Assist memory a, uint256[] memory rho, uint256 bits, uint256 words) internal pure {
        uint256 gAt = twistedEq(a.gamma, rho, a.point);
        uint256 eAt = K.eqProduct(W.ptr(rho), W.ptr(a.point), rho.length);
        if (a.anchor != F.mul(gAt, bits) ^ F.mul(eAt, words)) revert Layout();
    }
}
