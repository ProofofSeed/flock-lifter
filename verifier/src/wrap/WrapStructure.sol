// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Transcript} from "../Transcript.sol";
import {F} from "./F.sol";
import {W} from "./W.sol";
import {Whir, WhirClaim} from "./Whir.sol";
import {WrapKey} from "./WrapKey.sol";
import {Run, WrapPiop} from "./WrapPiop.sol";

/// What a claim on one of the block's matrices contributes to the sumchecks.
struct Side {
    /// The row and column points' bit coordinates.
    uint256[] a;
    uint256[] b;
    /// The row and column points' word coordinates, padded to a descriptor's.
    uint256[] xr;
    uint256[] xc;
    /// The sub-blocks' weight on the Keccak tensor.
    uint256 weight;
    /// The weight of a Keccak row's read of the constant wire.
    uint256 constantWeight;
    /// The claimed value.
    uint256 value;
}

/// A claim on a committed table folded to a point.
struct Folded {
    uint256[] row;
    uint256[] col;
    uint256 value;
}

/// The working state of the proof's verification.
struct Structure {
    uint256 tr;
    uint256 p;
    Side[2] sides;
    Folded[] folded;
    uint256[] coefficients;
    uint256[] tau;
    uint256[] opsPoint;
    uint256[] kernelPoint;
    uint256[] cellsPoint;
    uint256[] smallPoint;
    uint256 maskAt;
    uint256 kernelAt;
    uint256 cellsAt;
    uint256 smallAt;
}

/// The proof that the evaluations a wrap's outer proof leaves of the fixed tables are the
/// committed tables': the table claims' folds, four sumchecks down to bits of the committed bytes,
/// those bits from the bytes at Frobenius conjugates, and one opening.
library WrapStructure {
    uint256 internal constant LOW = 6;
    uint256 internal constant WORD_LOG = 10;
    uint256 internal constant WORD_BITS = 22;
    uint256 internal constant OP_BITS = 53;
    uint256 internal constant KERNEL_LOG = 27;

    error Shape();
    error Fold();
    error Operations();
    error Kernel();
    error Cells();
    error Small();
    error Roots();
    error Bits();

    /// Replays a sumcheck of `vars` rounds of degree `degree` from `claim`, reading its messages
    /// at the cursor; returns the final claim and the point.
    function sumcheck(Structure memory st, uint256 degree, uint256 vars, uint256 claim)
        internal
        pure
        returns (uint256, uint256[] memory point)
    {
        uint256 tr = st.tr;
        uint256 p = st.p;
        uint256 bits = WrapPiop.bitsFor(degree);
        point = new uint256[](vars);
        for (uint256 i = 0; i < vars; ++i) {
            Transcript.observeSliceFromCalldata(tr, p, degree);
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p + 16 * degree), bits);
            uint256 linear = claim;
            uint256 acc;
            for (uint256 k = degree - 1; k > 0; --k) {
                uint256 c = Calldata.f128(p + 16 * k);
                linear ^= c;
                acc = F.mul(acc, r) ^ c;
            }
            claim = F.mul(F.mul(acc, r) ^ linear, r) ^ Calldata.f128(p);
            point[i] = r;
            p += 16 * degree + 8;
        }
        st.p = p;
        return (claim, point);
    }

    /// `Π_i (1 + p[pi + i] + v[vi + i])` over `n` coordinates.
    function eq(uint256[] memory p, uint256 pi, uint256[] memory v, uint256 vi, uint256 n) internal pure returns (uint256 acc) {
        acc = 1;
        for (uint256 i = 0; i < n; ++i) {
            acc = F.mul(acc, 1 ^ p[pi + i] ^ v[vi + i]);
        }
    }

    /// `Σ_{t,u} eq(x, t)·eq(y, u)·eq(b, (t + u) mod 64)` over six coordinates each, `y` starting
    /// at `yi`.
    function rotatedEq(uint256[] memory x, uint256[] memory y, uint256 yi, uint256[] memory b) internal pure returns (uint256) {
        uint256 v0 = 1;
        uint256 v1 = 0;
        for (uint256 i = 0; i < LOW; ++i) {
            uint256 xi = x[i];
            uint256 yv = y[yi + i];
            uint256 bi = b[i];
            uint256 both = F.mul(xi, yv);
            uint256 w0 = 1 ^ xi ^ yv ^ both;
            uint256 w1 = xi ^ yv;
            // The weights of the sum bit being 0 and 1 are `1 + b_i` and `b_i`.
            uint256 w0b = F.mul(w0, bi);
            uint256 w1b = F.mul(w1, bi);
            uint256 w2b = F.mul(both, bi);
            (v0, v1) = (
                F.mul(v0, w0 ^ w0b ^ w1b) ^ F.mul(v1, w0b),
                F.mul(v0, both ^ w2b) ^ F.mul(v1, w1 ^ w1b ^ w2b)
            );
        }
        return v0 ^ v1;
    }

    /// `Σ_{j<n} Π_i g_i(bit i of j)` for `g_i(0) = g0[i]`, `g_i(1) = g1[i]`.
    function _prefixProductSum(uint256[] memory g0, uint256[] memory g1, uint256 n) private pure returns (uint256 acc) {
        uint256 k = g0.length;
        uint256[] memory full = new uint256[](k + 1);
        full[0] = 1;
        for (uint256 i = 0; i < k; ++i) {
            full[i + 1] = F.mul(full[i], g0[i] ^ g1[i]);
        }
        if (n == 1 << k) return full[k];
        uint256 high = 1;
        for (uint256 i = k; i > 0; --i) {
            if ((n >> (i - 1)) & 1 == 1) {
                acc ^= F.mul(F.mul(high, g0[i - 1]), full[i - 1]);
                high = F.mul(high, g1[i - 1]);
            } else {
                high = F.mul(high, g0[i - 1]);
            }
        }
    }

    /// The block claim on side `s`, read from the public segment at memory `pub`.
    function _side(uint256 pub, uint256 s) private pure returns (Side memory sd, uint256[] memory row, uint256[] memory col) {
        bytes memory acc = WrapKey.ACC;
        uint256 at = W.entry(acc, 3 * s, 4);
        uint256 k = WrapKey.K_LOG;
        if (W.entry(acc, 3 * s + 1, 4) != k || W.entry(acc, 3 * s + 2, 4) != k) revert Shape();
        row = new uint256[](k);
        col = new uint256[](k);
        for (uint256 i = 0; i < k; ++i) {
            col[i] = _word(pub, at + i);
            row[i] = _word(pub, at + k + i);
        }
        sd.value = _word(pub, at + 2 * k);
        sd.a = new uint256[](LOW);
        sd.b = new uint256[](LOW);
        sd.xr = new uint256[](WORD_BITS);
        sd.xc = new uint256[](WORD_BITS);
        for (uint256 i = 0; i < LOW; ++i) {
            sd.a[i] = row[i];
            sd.b[i] = col[i];
        }
        for (uint256 i = LOW; i < k; ++i) {
            sd.xr[i - LOW] = row[i];
            sd.xc[i - LOW] = col[i];
        }
        uint256 high = k - LOW - WORD_LOG;
        uint256[] memory b0 = new uint256[](high);
        uint256[] memory b1 = new uint256[](high);
        uint256[] memory r0 = new uint256[](high);
        uint256[] memory r1 = new uint256[](high);
        for (uint256 i = 0; i < high; ++i) {
            uint256 pr = row[LOW + WORD_LOG + i];
            uint256 q = col[LOW + WORD_LOG + i];
            b1[i] = F.mul(pr, q);
            b0[i] = 1 ^ pr ^ q ^ b1[i];
            r0[i] = 1 ^ pr;
            r1[i] = pr;
        }
        uint256 from = WrapKey.HEAD_SUBS;
        uint256 to = from + WrapKey.KECCAK_SUBS;
        sd.weight = _prefixProductSum(b0, b1, to) ^ _prefixProductSum(b0, b1, from);
        uint256 atConstant = 1;
        for (uint256 i = 0; i < k; ++i) {
            atConstant = F.mul(atConstant, 1 ^ col[i]);
        }
        sd.constantWeight = F.mul(_prefixProductSum(r0, r1, to) ^ _prefixProductSum(r0, r1, from), atConstant);
    }

    function _word(uint256 pub, uint256 i) private pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(128, mload(add(pub, shl(4, i))))
        }
    }

    function _observeArray(uint256 tr, uint256[] memory v, uint256 from, uint256 n) private pure {
        uint256 at;
        assembly ("memory-safe") {
            at := add(add(v, 0x20), shl(5, from))
        }
        W.observeWords(tr, at, n);
    }

    /// The multilinear extension of a weight `low ⊗ eq(point)` at `rho`: `low` has 64 entries and
    /// `point` is `point[0 .. n)`.
    function _weightEval(uint256[] memory low, uint256[] memory point, uint256 n, uint256[] memory rho) private pure returns (uint256 acc) {
        uint256[] memory v = new uint256[](32);
        uint256 r = rho[0];
        for (uint256 k = 0; k < 32; ++k) {
            v[k] = low[2 * k] ^ F.mul(r, low[2 * k] ^ low[2 * k + 1]);
        }
        uint256 len = 32;
        for (uint256 j = 1; j < LOW; ++j) {
            r = rho[j];
            len >>= 1;
            for (uint256 k = 0; k < len; ++k) {
                v[k] = v[2 * k] ^ F.mul(r, v[2 * k] ^ v[2 * k + 1]);
            }
        }
        acc = v[0];
        for (uint256 i = 0; i < n; ++i) {
            acc = F.mul(acc, 1 ^ point[i] ^ rho[LOW + i]);
        }
    }

    /// One fold of the claims on a side of a committed table of `2^k` rows: the table types
    /// `types` share it, their claims share the weights `(skip, xInner)` and `(zPartial, rr)`, and
    /// their values sit at `evalsAt`, 32 bytes a type.
    function _fold(
        Structure memory st,
        Run memory x,
        uint256 k,
        uint256[] memory types,
        uint256[] memory xInner,
        uint256[] memory zPartial,
        uint256 valueOffset
    ) private pure returns (Folded memory out) {
        uint256 tr = st.tr;
        uint256 p = st.p;
        uint256 inner = k - LOW;
        uint256 n = types.length;
        Transcript.label(tr, WrapKey.L_FOLD_0, WrapKey.L_FOLD_1, WrapKey.L_FOLD_LEN);
        for (uint256 c = 0; c < n; ++c) {
            _observeArray(tr, x.skipC, 0, 64);
            _observeArray(tr, xInner, 0, inner);
            Transcript.observeSliceFromCalldata(tr, x.zPartialAt, 64);
            _observeArray(tr, x.rr, 0, inner);
            Transcript.observe(tr, Calldata.f128(x.evalsAt + 32 * types[c] + valueOffset));
        }
        uint256[] memory lambdas = Transcript.powSampleVec(tr, Calldata.nonce(p), 1, n);
        p += 8;
        uint256 running;
        for (uint256 c = 0; c < n; ++c) {
            running ^= F.mul(lambdas[c], Calldata.f128(x.evalsAt + 32 * types[c] + valueOffset));
        }
        (p, running, out.col) = _rounds(tr, p, k, running);
        {
            uint256 expect;
            for (uint256 c = 0; c < n; ++c) {
                uint256 g = Calldata.f128(p + 16 * c);
                Transcript.observe(tr, g);
                expect ^= F.mul(lambdas[c], g);
            }
            if (running != F.mul(expect, _weightEval(zPartial, x.rr, inner, out.col))) revert Fold();
        }
        uint256 bridgeAt = p;
        p += 16 * n;
        uint256[] memory mus = Transcript.powSampleVec(tr, Calldata.nonce(p), 1, n);
        p += 8;
        running = 0;
        uint256 muSum;
        for (uint256 c = 0; c < n; ++c) {
            running ^= F.mul(mus[c], Calldata.f128(bridgeAt + 16 * c));
            muSum ^= mus[c];
        }
        (p, running, out.row) = _rounds(tr, p, k, running);
        out.value = Calldata.f128(p);
        if (running != F.mul(F.mul(muSum, _weightEval(x.skipC, xInner, inner, out.row)), out.value)) revert Fold();
        Transcript.observe(tr, out.value);
        st.p = p + 16;
    }

    /// `k` quadratic rounds read at `p`.
    function _rounds(uint256 tr, uint256 p, uint256 k, uint256 running) private pure returns (uint256, uint256, uint256[] memory rho) {
        rho = new uint256[](k);
        for (uint256 i = 0; i < k; ++i) {
            uint256 q1 = Calldata.f128(p);
            uint256 qinf = Calldata.f128(p + 16);
            Transcript.observe(tr, q1);
            Transcript.observe(tr, qinf);
            uint256 r = Transcript.powSample(tr, Calldata.nonce(p + 32), 2);
            p += 40;
            running = W.quadratic(running, q1, qinf, r);
            rho[i] = r;
        }
        return (p, running, rho);
    }

    /// Binds the claims and folds every table's.
    function _folds(Structure memory st, Run memory x) private pure {
        uint256 tr = st.tr;
        Transcript.label(tr, WrapKey.L_STRUCTURE_0, WrapKey.L_STRUCTURE_1, WrapKey.L_STRUCTURE_LEN);
        for (uint256 s = 0; s < 2; ++s) {
            uint256[] memory row;
            uint256[] memory col;
            (st.sides[s], row, col) = _side(x.pub, s);
            _observeArray(tr, row, 0, row.length);
            _observeArray(tr, col, 0, col.length);
            Transcript.observe(tr, st.sides[s].value);
        }
        _observeArray(tr, x.rho, 0, x.rho.length);
        {
            uint256[] memory cells = new uint256[](3);
            cells[0] = x.live;
            cells[1] = x.masked;
            cells[2] = x.sigma;
            _observeArray(tr, cells, 0, 3);
        }
        uint256 rounds = WrapKey.M_BOOL - WrapKey.NU - LOW;
        uint256[] memory xInner = new uint256[](rounds);
        xInner[0] = x.mlv[0];
        for (uint256 i = 1; i < rounds; ++i) {
            xInner[i] = x.mlv[WrapKey.NU + i];
        }
        uint256[] memory zPartial = new uint256[](64);
        for (uint256 i = 0; i < 64; ++i) {
            zPartial[i] = Calldata.f128(x.zPartialAt + 16 * i);
        }
        bytes memory bools = WrapKey.BOOLS;
        bytes memory tables = WrapKey.TABLES;
        st.folded = new Folded[](2 * WrapKey.N_TABLES);
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            uint256 count;
            for (uint256 i = 0; i < WrapKey.N_BOOL; ++i) {
                if (W.read(bools, 12 * i + 2, 1) == t) ++count;
            }
            uint256[] memory types = new uint256[](count);
            count = 0;
            for (uint256 i = 0; i < WrapKey.N_BOOL; ++i) {
                if (W.read(bools, 12 * i + 2, 1) == t) types[count++] = i;
            }
            uint256 k = W.read(tables, 12 * t, 1);
            st.folded[2 * t] = _fold(st, x, k, types, xInner, zPartial, 0);
            st.folded[2 * t + 1] = _fold(st, x, k, types, xInner, zPartial, 16);
        }
    }

    /// The operations sumcheck's term at the final point: the mask, then a descriptor's bits, at
    /// calldata `at`.
    function _opsTerm(Structure memory st, uint256 at) private pure returns (uint256) {
        uint256[] memory bits = new uint256[](OP_BITS);
        for (uint256 i = 0; i < OP_BITS; ++i) {
            bits[i] = Calldata.f128(at + 16 * (1 + i));
        }
        uint256 acc;
        for (uint256 s = 0; s < 2; ++s) {
            Side memory sd = st.sides[s];
            uint256 read = F.mul(bits[2], eq(sd.b, 0, bits, 3, LOW)) ^ F.mul(1 ^ bits[2], rotatedEq(st.tau, bits, 3, sd.b));
            uint256 term = F.mul(
                1 ^ bits[0], F.mul(F.mul(eq(sd.xr, 0, bits, 9, WORD_BITS), eq(sd.xc, 0, bits, 9 + WORD_BITS, WORD_BITS)), read)
            ) ^ F.mul(bits[0], F.mul(eq(sd.xr, 0, bits, 9, WORD_LOG), sd.constantWeight));
            uint256 select = s == 0 ? 1 ^ bits[1] : bits[1];
            acc ^= F.mul(F.mul(st.coefficients[s], eq(sd.a, 0, st.tau, 0, LOW)), F.mul(select, term));
        }
        return F.mul(Calldata.f128(at), acc);
    }

    /// The Keccak tensor's weight at the point `theta` over its offset, column word, row word and
    /// side.
    function _kernelWeight(Structure memory st, uint256[] memory theta) private pure returns (uint256 acc) {
        for (uint256 s = 0; s < 2; ++s) {
            Side memory sd = st.sides[s];
            uint256 select = s == 0 ? 1 ^ theta[KERNEL_LOG - 1] : theta[KERNEL_LOG - 1];
            acc ^= F.mul(
                F.mul(st.coefficients[2 + s], select),
                F.mul(
                    F.mul(eq(sd.xr, 0, theta, LOW + WORD_LOG, WORD_LOG), eq(sd.xc, 0, theta, LOW, WORD_LOG)),
                    rotatedEq(sd.a, theta, 0, sd.b)
                )
            );
        }
    }

    /// The field element whose bits are the `n` values at calldata `at`, bit `i` weighing `x^i`.
    function _embedded(uint256 at, uint256 n) private pure returns (uint256 acc) {
        for (uint256 i = 0; i < n; ++i) {
            acc ^= F.mul(Calldata.f128(at + 16 * i), 1 << i);
        }
    }

    /// The live cells' term at the final point: the live flag, a cell's bits and its image's, at
    /// calldata `at`.
    function _cellsTerm(Structure memory st, Run memory x, uint256 at) private pure returns (uint256) {
        uint256 mu = WrapKey.MU;
        uint256 e = 1;
        for (uint256 i = 0; i < mu; ++i) {
            e = F.mul(e, 1 ^ x.rho[i] ^ Calldata.f128(at + 16 * (1 + i)));
        }
        uint256 inner = st.coefficients[4] ^ F.mul(st.coefficients[5], _embedded(at + 16, mu))
            ^ F.mul(st.coefficients[6], _embedded(at + 16 * (1 + mu), mu));
        return F.mul(F.mul(Calldata.f128(at), e), inner);
    }

    /// The four sumchecks, from the batching coefficients to the small entries.
    function _sumchecks(Structure memory st, Run memory x) private {
        uint256 tr = st.tr;
        uint256 p = st.p;
        bytes memory tables = WrapKey.TABLES;
        bytes memory regions = WrapKey.REGIONS;
        uint256 nSmall;
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            if (W.read(tables, 12 * t + 1, 1) == 1) nSmall += 2;
        }
        uint256 kv0 = Calldata.f128(p);
        uint256 kv1 = Calldata.f128(p + 16);
        Transcript.observeSliceFromCalldata(tr, p, 2);
        st.coefficients = Transcript.powSampleVec(tr, Calldata.nonce(p + 32), 1, 7 + nSmall);
        st.p = p + 40;
        uint256 claim = F.mul(st.coefficients[0], st.sides[0].value ^ F.mul(st.sides[0].weight, kv0))
            ^ F.mul(st.coefficients[1], st.sides[1].value ^ F.mul(st.sides[1].weight, kv1));
        (claim, st.tau) = sumcheck(st, 3, LOW, claim);
        W.mark(12, tr);
        (claim, st.opsPoint) = sumcheck(st, OP_BITS + 1, W.read(regions, 4, 1) - 3, claim);
        st.maskAt = st.p;
        if (claim != _opsTerm(st, st.p)) revert Operations();
        Transcript.observe(tr, Calldata.f128(st.p));
        Transcript.observeSliceFromCalldata(tr, st.p + 16, OP_BITS);
        st.p += 16 * (1 + OP_BITS);
        W.mark(13, tr);

        claim = F.mul(st.coefficients[2], kv0) ^ F.mul(st.coefficients[3], kv1);
        (claim, st.kernelPoint) = sumcheck(st, 2, KERNEL_LOG, claim);
        st.kernelAt = st.p;
        if (claim != F.mul(Calldata.f128(st.p), _kernelWeight(st, st.kernelPoint))) revert Kernel();
        Transcript.observe(tr, Calldata.f128(st.p));
        st.p += 16;
        W.mark(14, tr);

        uint256 mu = WrapKey.MU;
        claim = F.mul(st.coefficients[4], x.live) ^ F.mul(st.coefficients[5], x.masked) ^ F.mul(st.coefficients[6], x.sigma);
        (claim, st.cellsPoint) = sumcheck(st, mu + 2, W.read(regions, 19, 1) - 3, claim);
        st.cellsAt = st.p;
        if (claim != _cellsTerm(st, x, st.p)) revert Cells();
        Transcript.observeSliceFromCalldata(tr, st.p, 1 + 2 * mu);
        st.p += 16 * (1 + 2 * mu);
        W.mark(15, tr);

        _small(st, tables, regions);
        W.mark(16, tr);
    }

    /// The small entries' sumcheck over the folded claims on the tables held as entries.
    function _small(Structure memory st, bytes memory tables, bytes memory regions) private pure {
        uint256 id = WrapKey.SMALL_ID;
        uint256 index = WrapKey.SMALL_INDEX;
        uint256 width = 1 + id + 2 * index;
        uint256 claim;
        uint256 n;
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            if (W.read(tables, 12 * t + 1, 1) == 1) {
                claim ^= F.mul(st.coefficients[7 + n], st.folded[2 * t].value) ^ F.mul(st.coefficients[8 + n], st.folded[2 * t + 1].value);
                n += 2;
            }
        }
        (claim, st.smallPoint) = sumcheck(st, width, W.read(regions, 24, 1) - 3, claim);
        st.smallAt = st.p;
        uint256 at = st.p;
        uint256[] memory bits = new uint256[](width);
        for (uint256 i = 0; i < width; ++i) {
            bits[i] = Calldata.f128(at + 16 * i);
        }
        uint256 sum;
        n = 0;
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            if (W.read(tables, 12 * t + 1, 1) == 0) continue;
            uint256 k = W.read(tables, 12 * t, 1);
            for (uint256 side = 0; side < 2; ++side) {
                Folded memory f = st.folded[2 * t + side];
                uint256 e = W.eqWeight(bits, 1, id, W.read(tables, 12 * t + 2, 1) + side);
                // The claim's points are padded with zeros to the entries' index width.
                e = F.mul(e, eq(f.row, 0, bits, 1 + id, k));
                e = F.mul(e, eq(f.col, 0, bits, 1 + id + index, k));
                for (uint256 i = k; i < index; ++i) {
                    e = F.mul(e, F.mul(1 ^ bits[1 + id + i], 1 ^ bits[1 + id + index + i]));
                }
                sum ^= F.mul(st.coefficients[7 + n], e);
                ++n;
            }
        }
        if (claim != F.mul(bits[0], sum)) revert Small();
        Transcript.observeSliceFromCalldata(st.tr, at, width);
        st.p = at + 16 * width;
    }

    /// The point over the committed bytes' bits of a region's local point: `local`, then the bits
    /// of the region's index.
    function _lift(uint256[] memory local, uint256 offset, uint256 log) private pure returns (uint256[] memory point) {
        uint256 n = WrapKey.STRUCT_N;
        if (local.length != 3 + log) revert Shape();
        point = new uint256[](3 + n);
        for (uint256 i = 0; i < local.length; ++i) {
            point[i] = local[i];
        }
        uint256 prefix = offset >> log;
        for (uint256 i = 0; i < n - log; ++i) {
            point[3 + log + i] = (prefix >> i) & 1;
        }
    }

    function _concat(uint256[] memory a, uint256[] memory b) private pure returns (uint256[] memory c) {
        c = new uint256[](a.length + b.length);
        for (uint256 i = 0; i < a.length; ++i) {
            c[i] = a[i];
        }
        for (uint256 i = 0; i < b.length; ++i) {
            c[a.length + i] = b[i];
        }
    }

    /// `Σ_i eq(zeta[from .. from + 6), i)·bits[i]` over the `n` values at calldata `at`.
    function _batched(uint256[] memory zeta, uint256 from, uint256 at, uint256 n) private pure returns (uint256 acc) {
        uint256[] memory e = W.eqTable(zeta, from, LOW, 1);
        for (uint256 i = 0; i < n; ++i) {
            acc ^= F.mul(e[i], Calldata.f128(at + 16 * i));
        }
    }

    function _slice(uint256[] memory v, uint256 from, uint256 n) private pure returns (uint256[] memory s) {
        s = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            s[i] = v[from + i];
        }
    }

    /// The claims on the committed bytes' bits: their points and values, in the proof's order.
    function _bitClaims(Structure memory st, uint256[] memory zeta)
        private
        pure
        returns (uint256[][] memory points, uint256[] memory values)
    {
        bytes memory tables = WrapKey.TABLES;
        bytes memory regions = WrapKey.REGIONS;
        uint256 dense;
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            if (W.read(tables, 12 * t + 1, 1) == 0) dense += 2;
        }
        points = new uint256[][](dense + 5);
        values = new uint256[](dense + 5);
        uint256 n;
        for (uint256 t = 0; t < WrapKey.N_TABLES; ++t) {
            if (W.read(tables, 12 * t + 1, 1) == 1) continue;
            for (uint256 side = 0; side < 2; ++side) {
                Folded memory f = st.folded[2 * t + side];
                points[n] = _lift(_concat(f.col, f.row), W.read(tables, 12 * t + 2 + 5 * side, 4), W.read(tables, 12 * t + 6 + 5 * side, 1));
                values[n++] = f.value;
            }
        }
        points[n] = _lift(_concat(_slice(zeta, 0, LOW), st.opsPoint), W.read(regions, 0, 4), W.read(regions, 4, 1));
        values[n++] = _batched(zeta, 0, st.maskAt + 16, OP_BITS);
        points[n] = _lift(_concat(st.tau, st.opsPoint), W.read(regions, 5, 4), W.read(regions, 9, 1));
        values[n++] = Calldata.f128(st.maskAt);
        points[n] = _lift(st.kernelPoint, W.read(regions, 10, 4), W.read(regions, 14, 1));
        values[n++] = Calldata.f128(st.kernelAt);
        points[n] = _lift(_concat(_slice(zeta, LOW, LOW), st.cellsPoint), W.read(regions, 15, 4), W.read(regions, 19, 1));
        values[n++] = _batched(zeta, LOW, st.cellsAt, 1 + 2 * WrapKey.MU);
        points[n] = _lift(_concat(_slice(zeta, 2 * LOW, LOW), st.smallPoint), W.read(regions, 20, 4), W.read(regions, 24, 1));
        values[n] = _batched(zeta, 2 * LOW, st.smallAt, 1 + WrapKey.SMALL_ID + 2 * WrapKey.SMALL_INDEX);
    }

    /// The extension of a table of bits packed in bytes at a point whose three low coordinates are
    /// `point[0 .. 3)`, from the bytes' extension at the eight conjugates of the rest of the point,
    /// at calldata `at`.
    function _bitValue(uint256[] memory point, uint256 at, bytes memory dual) private pure returns (uint256 acc) {
        uint256[] memory powers = new uint256[](8);
        for (uint256 j = 0; j < 8; ++j) {
            powers[j] = F.frob(Calldata.f128(at + 16 * j), j);
        }
        uint256[] memory e = W.eqTable(point, 0, 3, 1);
        for (uint256 i = 0; i < 8; ++i) {
            uint256 b;
            for (uint256 j = 0; j < 8; ++j) {
                b ^= F.mul(W.entry(dual, 8 * i + j, 16), powers[j]);
            }
            acc ^= F.mul(b, e[i]);
        }
    }

    /// Verifies the proof at the cursor of the claims `x` holds.
    function verify(Run memory x) internal {
        Structure memory st;
        st.tr = x.tr;
        st.p = x.p;
        _folds(st, x);
        W.mark(11, st.tr);
        _sumchecks(st, x);
        uint256[] memory zeta = Transcript.powSampleVec(st.tr, Calldata.nonce(st.p), 3, 3 * LOW);
        st.p += 8;
        (uint256[][] memory claims, uint256[] memory claimed) = _bitClaims(st, zeta);
        WhirClaim memory c;
        uint256 n = WrapKey.STRUCT_N;
        c.points = new uint256[][](8 * claims.length);
        c.values = new uint256[](8 * claims.length);
        bytes memory dual = WrapKey.DUAL;
        uint256 p = st.p;
        for (uint256 k = 0; k < claims.length; ++k) {
            uint256[] memory previous = _slice(claims[k], 3, n);
            c.points[8 * k] = previous;
            for (uint256 j = 1; j < 8; ++j) {
                uint256[] memory root = new uint256[](n);
                for (uint256 i = 0; i < n; ++i) {
                    root[i] = Calldata.f128(p + 16 * i);
                    if (F.sq(root[i]) != previous[i]) revert Roots();
                }
                p += 16 * n;
                c.points[8 * k + j] = root;
                previous = root;
            }
            if (_bitValue(claims[k], p, dual) != claimed[k]) revert Bits();
            for (uint256 j = 0; j < 8; ++j) {
                c.values[8 * k + j] = Calldata.f128(p + 16 * j);
            }
            p += 128;
        }
        W.mark(17, st.tr);
        c.rounds = WrapKey.STRUCT_ROUNDS;
        c.finalVars = WrapKey.STRUCT_FINAL;
        c.powBits = WrapKey.STRUCT_POW;
        bytes memory cap = WrapKey.STRUCT_CAP;
        uint256 capAt;
        assembly ("memory-safe") {
            capAt := add(cap, 0x20)
        }
        c.cap = capAt;
        W.append(st.tr, WrapKey.STRUCT_START);
        x.p = Whir.verify(st.tr, c, p);
    }
}
