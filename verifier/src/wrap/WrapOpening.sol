// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
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
    uint256 child;
}

/// One ring-switched claim: its point's equality table, its point, and its switched sum.
struct Switched {
    uint256[] r;
    uint256[] eq;
    uint256 sum;
}

/// The assist's working state.
struct Assist {
    uint256 ch;
    uint256 p;
    uint256 gamma;
    uint256[4] gpow;
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
        uint256 acc;
        for (uint256 i = 0; i < 64; ++i) {
            uint256 lo = Calldata.f128(p + 16 * i);
            acc ^= F.mul(skip[i], lo ^ F.mul(x0, lo ^ Calldata.f128(p + 16 * (64 + i))));
        }
        if (acc != value) revert RingSwitchClaim();
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

    /// The coefficients `c_j` with `Σ_t bit_t(v)·gamma·eq(r, t) = Σ_j c_j·v^(2^j)` for every word
    /// `v`, from the trace-dual of the polynomial basis.
    function coefficients(uint256 gamma, uint256[] memory r, uint256[] memory eq) internal pure returns (uint256[] memory c) {
        bytes memory beta = WrapKey.BETA;
        bytes memory dinv = WrapKey.DINV;
        c = new uint256[](128);
        uint256 tail = eq[0] ^ eq[1];
        for (uint256 j = 0; j < 128; ++j) {
            uint256 top = gamma;
            for (uint256 i = 0; i < 7; ++i) {
                top = F.mul(top, r[i] ^ F.mul(1 ^ r[i], W.entry(beta, (j + i) & 127, 16)));
            }
            uint256 b = W.entry(beta, j, 16);
            uint256 low = eq[0];
            for (uint256 t = 1; t < 7; ++t) {
                low = F.mul(low, b) ^ eq[t];
            }
            c[j] = F.mul(W.entry(dinv, j, 16), top ^ F.mul(gamma, low ^ F.mul(eq[0], b) ^ tail));
        }
    }

    /// `Σ_j gamma^j·eq(rho^(2^-j), x)` over the 128 inverse Frobenius powers of `rho`, as the
    /// square of a chain of squarings over `Π_i (1 + rho_i + x_i^(2^j))`.
    function twistedEq(uint256 gamma, uint256[] memory rho, uint256[] memory x) internal pure returns (uint256 acc) {
        uint256 n = rho.length;
        uint256[] memory powers = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            powers[i] = x[i];
        }
        uint256 g = gamma;
        uint256 e = 1;
        for (uint256 j = 0; j < 128; ++j) {
            if (j > 0) {
                for (uint256 i = 0; i < n; ++i) {
                    powers[i] = F.sq(powers[i]);
                }
                g = F.sq(g);
                e = F.mul(F.sq(e), g);
            }
            uint256 eq = 1;
            for (uint256 i = 0; i < n; ++i) {
                eq = F.mul(eq, 1 ^ rho[i] ^ powers[i]);
            }
            acc = F.sq(acc) ^ F.mul(e, eq);
        }
        acc = F.sq(acc);
    }

    /// `Σ_j c[j]·v_j^(2^j)` over the 128 values at calldata `at`.
    function frobeniusSum(uint256[] memory c, uint256 at) internal pure returns (uint256 acc) {
        for (uint256 j = 0; j < 128; ++j) {
            acc ^= F.mul(c[j], F.frob(Calldata.f128(at + 16 * j), j));
        }
    }

    function _differ(uint256[] memory a, uint256 ai, uint256[] memory b, uint256 bi, uint256 n) private pure returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            if (a[ai + i] != b[bi + i]) return true;
        }
        return false;
    }

    /// The transport of the claims `x` holds, up to the opening of the committed stack; the
    /// assist runs on a fork of the transcript, which is returned for merging after that opening.
    function transport(Run memory x) internal returns (Opened memory o) {
        uint256 tr = x.tr;
        uint256 p = x.p;
        Transcript.label(tr, L_MERGED_0, L_MERGED_1, 48);
        Switched[2] memory sw;
        sw[0] = ringSwitch(tr, x.skipAb, x.rr[0], x.lcValue, p);
        p += 128 * 16 + 8;
        x.skipC = W.lagrange(x.phi, x.zcZ);
        sw[1] = ringSwitch(tr, x.skipC, x.rRest[0], x.zcC, p);
        p += 128 * 16 + 8;
        Transcript.observe(tr, x.ec);
        Transcript.observe(tr, x.zEval);
        for (uint256 i = 0; i < WrapKey.N_GATE; ++i) {
            Transcript.observe(tr, Calldata.f128(x.gatherAt + 16 * i));
        }
        uint256[] memory gammas = Transcript.powSampleVec(tr, Calldata.nonce(p), 6, 4 + WrapKey.N_GATE);
        p += 8;
        uint256 running = F.mul(gammas[0], sw[0].sum) ^ F.mul(gammas[1], sw[1].sum) ^ F.mul(gammas[2], x.ec) ^ F.mul(gammas[3], x.zEval);
        for (uint256 i = 0; i < WrapKey.N_GATE; ++i) {
            running ^= F.mul(gammas[4 + i], Calldata.f128(x.gatherAt + 16 * i));
        }
        o.rho = new uint256[](WrapKey.DENSE_LOG);
        for (uint256 i = 0; i < WrapKey.DENSE_LOG; ++i) {
            uint256 g1 = Calldata.f128(p);
            uint256 ginf = Calldata.f128(p + 16);
            Transcript.observe(tr, g1);
            Transcript.observe(tr, ginf);
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            running = W.quadratic(running, g1, ginf, r);
            o.rho[i] = r;
        }
        o.value = Calldata.f128(p);
        o.target = running;
        p += 16;
        W.mark(6, tr);
        uint256 nu = WrapKey.NU;
        if (
            !_differ(x.mlv, 1, x.rRest, 1, nu) || !_differ(x.mlv, 1, x.er, 0, nu) || !_differ(x.mlv, 1, x.rho, 0, nu)
                || !_differ(x.rRest, 1, x.er, 0, nu) || !_differ(x.rRest, 1, x.rho, 0, nu) || !_differ(x.er, 0, x.rho, 0, nu)
        ) revert RowPoints();
        Assist memory a;
        a.ch = W.fork(tr, "flock-par-assist-v1", 1 << 15);
        a.p = p;
        _multipoint(a, o.rho);
        W.mark(7, a.ch);
        _anchor(a);
        W.mark(8, a.ch);
        _layout(x, a, o.rho, gammas);
        if (a.claim != a.v) revert Multipoint();
        o.weight = frobeniusSum(coefficients(gammas[0], sw[0].r, sw[0].eq), a.valuesAt)
            ^ frobeniusSum(coefficients(gammas[1], sw[1].r, sw[1].eq), a.valuesAt + 128 * 16)
            ^ Calldata.f128(a.valuesAt + 256 * 16) ^ Calldata.f128(a.valuesAt + 257 * 16);
        o.child = a.ch;
        x.p = a.p;
    }

    /// The multipoint reduction of the dual values: their batching and its sumcheck.
    function _multipoint(Assist memory a, uint256[] memory rho) private pure {
        uint256 ch = a.ch;
        uint256 p = a.p;
        uint256 m = rho.length;
        Transcript.label(ch, L_MULTI_0, L_MULTI_1, 48);
        a.valuesAt = p;
        for (uint256 i = 0; i < 258; ++i) {
            Transcript.observe(ch, Calldata.f128(p + 16 * i));
        }
        p += 258 * 16;
        a.gamma = Transcript.powSample(ch, Calldata.nonce(p), 9);
        p += 8;
        uint256 power = 1;
        uint256 claim;
        for (uint256 i = 0; i < 258; ++i) {
            if (i == 0) a.gpow[0] = power;
            if (i == 128) a.gpow[1] = power;
            if (i == 256) a.gpow[2] = power;
            if (i == 257) a.gpow[3] = power;
            claim ^= F.mul(power, Calldata.f128(a.valuesAt + 16 * i));
            power = F.mul(power, a.gamma);
        }
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

    /// The anchor's sumcheck over the boundary bits.
    function _anchor(Assist memory a) private pure {
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
        uint256[][3] memory tp;
        uint256[][3] memory tq;
        for (uint256 c = 0; c < 3; ++c) {
            uint256 n = layers - 8 * c < 8 ? layers - 8 * c : 8;
            tp[c] = W.eqTable(even, 8 * c, n, 1);
            tq[c] = W.eqTable(odd, 8 * c, n, 1);
        }
        uint256 count = runs.length / 12;
        at = new uint256[](count);
        for (uint256 r = 0; r < count; ++r) {
            uint256 t0 = W.read(runs, 12 * r, 4);
            uint256 t1 = W.read(runs, 12 * r + 4, 4);
            at[r] = F.mul(
                F.mul(F.mul(tp[0][t0 & 255], tp[1][(t0 >> 8) & 255]), tp[2][t0 >> 16]),
                F.mul(F.mul(tq[0][t1 & 255], tq[1][(t1 >> 8) & 255]), tq[2][t1 >> 16])
            );
        }
    }

    /// `Σ_runs at[run]·Σ_{columns of the run} table[column − base]`, the table taken as zero
    /// outside `[base, base + table.length)`.
    function _weigh(uint256[] memory table, uint256 base, bytes memory runs, uint256[] memory at) private pure returns (uint256 acc) {
        uint256 count = at.length;
        uint256 end = base + table.length;
        for (uint256 r = 0; r < count; ++r) {
            uint256 start = W.read(runs, 12 * r + 8, 2);
            uint256 stop = start + W.read(runs, 12 * r + 10, 2);
            if (stop <= base || start >= end) continue;
            if (start < base) start = base;
            if (stop > end) stop = end;
            uint256 sum;
            for (uint256 y = start; y < stop; ++y) {
                sum ^= table[y - base];
            }
            acc ^= F.mul(sum, at[r]);
        }
    }

    /// The branching program's value over the boundary bits at `sigma`, for the row point
    /// `row[from .. from + NU)` and the dense index `index`.
    function _boundary(uint256[] memory row, uint256 from, uint256[] memory index, uint256[] memory sigma, bytes memory tx)
        private
        pure
        returns (uint256)
    {
        uint256 layers = sigma.length / 2;
        uint256[4] memory g;
        g[2] = 1;
        uint256[16] memory prod;
        for (uint256 layer = layers; layer > 0; --layer) {
            uint256 l = layer - 1;
            uint256[4] memory eq4 = _pair(l < WrapKey.NU ? row[from + l] : 0, l < index.length ? index[l] : 0);
            uint256[4] memory e = _pair(sigma[2 * l], sigma[2 * l + 1]);
            for (uint256 i = 0; i < 4; ++i) {
                for (uint256 s = 0; s < 4; ++s) {
                    prod[4 * i + s] = F.mul(eq4[i], g[s]);
                }
            }
            uint256[4] memory prev;
            for (uint256 cd = 0; cd < 4; ++cd) {
                for (uint256 s = 0; s < 4; ++s) {
                    uint256 t = 4 * (4 * cd + s);
                    prev[s] ^= F.mul(
                        e[cd],
                        prod[4 * W.read(tx, t, 1) + W.read(tx, t + 1, 1)] ^ prod[4 * W.read(tx, t + 2, 1) + W.read(tx, t + 3, 1)]
                    );
                }
            }
            g = prev;
        }
        return g[0];
    }

    /// `[(1 + a)(1 + b), a(1 + b), (1 + a)b, ab]`.
    function _pair(uint256 a, uint256 b) private pure returns (uint256[4] memory t) {
        uint256 ab = F.mul(a, b);
        t[0] = 1 ^ a ^ b ^ ab;
        t[1] = a ^ ab;
        t[2] = b ^ ab;
        t[3] = ab;
    }

    /// Checks the anchor's last equation: every statement's layout weight and boundary value at
    /// the anchor's point.
    function _layout(Run memory x, Assist memory a, uint256[] memory rho, uint256[] memory gammas) private pure {
        bytes memory runs = WrapKey.RUNS;
        bytes memory tx = WrapKey.TRANSITIONS;
        uint256[] memory at = _atRuns(a.sigma, runs);
        uint256 gAt = twistedEq(a.gamma, rho, a.point);
        uint256 eAt = 1;
        for (uint256 i = 0; i < rho.length; ++i) {
            eAt = F.mul(eAt, 1 ^ rho[i] ^ a.point[i]);
        }
        uint256 nu = WrapKey.NU;
        uint256 low = WrapKey.M_BOOL - nu - 7;
        // The two claims on the committed bits: their column points end in zeros.
        uint256 expect = F.mul(
            F.mul(a.gpow[0], gAt), F.mul(_weigh(W.eqTable(x.rr, 1, low, 1), 0, runs, at), _boundary(x.mlv, 1, a.point, a.sigma, tx))
        );
        expect ^= F.mul(
            F.mul(a.gpow[1], gAt),
            F.mul(_weigh(W.eqTable(x.rRest, 1 + nu, low, 1), 0, runs, at), _boundary(x.rRest, 1, a.point, a.sigma, tx))
        );
        // The element class's two claims share their rows; their column points end in the region's frozen bits.
        {
            uint256 cols = x.ecol.length;
            uint256 base = WrapKey.ELEM_FROZEN << cols;
            uint256 w = _weigh(W.eqTable(x.er, nu, cols, gammas[2]), base, runs, at) ^ _weigh(W.eqTable(x.ecol, 0, cols, gammas[3]), base, runs, at);
            expect ^= F.mul(F.mul(a.gpow[2], eAt), F.mul(w, _boundary(x.er, 0, a.point, a.sigma, tx)));
        }
        // The gathered cell slots share the wiring point's rows; each reads one column.
        {
            bytes memory gateRuns = WrapKey.GATE_RUNS;
            uint256[] memory hot = new uint256[](at.length);
            for (uint256 i = 0; i < WrapKey.N_GATE; ++i) {
                hot[W.entry(gateRuns, i, 2)] ^= gammas[4 + i];
            }
            uint256 w;
            for (uint256 r = 0; r < at.length; ++r) {
                if (hot[r] != 0) w ^= F.mul(hot[r], at[r]);
            }
            expect ^= F.mul(F.mul(a.gpow[3], eAt), F.mul(w, _boundary(x.rho, 0, a.point, a.sigma, tx)));
        }
        if (a.anchor != expect) revert Layout();
    }
}
