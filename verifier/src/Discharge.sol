// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "./Constants.sol";
import {GF2} from "./GF2.sol";
import {Meter} from "./Meter.sol";
import {Piop} from "./Piop.sol";
import {Tables} from "./Tables.sol";

/// The lincheck's matrix discharge for one statement's response block: the fold of the
/// Keccak-f sub-blocks, evaluated once and re-weighted, and the block's other rows, read from a
/// calldata stream whose hash chain must end at the statement's pinned digest.
///
/// A claim is `4 + 2·(kLog − 6) + 64` words: `alpha, beta, z, running`, the row point, the column
/// point, then the collapsed witness `zp`. The rows never form the combination `comb` itself:
/// each adds its share of `Σ_t zp[t]·(α·A[t] + B[t])` to one scalar per claim, and its share of
/// the constant-wire B side to another.
///
/// The stream is a sequence of records (see `crates/evm/src/stream.rs`): explicit rows, words
/// of identity rows, and whole families of Keccak-f link rows, summed in closed form.
contract FlockDischarge {
    uint256 internal constant LO = 10;
    uint256 internal constant STATE24_BASE = 2048;
    uint256 internal constant T_BASE = 4160;
    uint256 internal constant PRG_BITS = 392;
    uint256 internal constant TAB = 4096 * 32;

    /// log2 of the block width.
    uint256 public immutable kLog;
    /// Sub-blocks before the first Keccak-f sub-block.
    uint256 public immutable headSubs;
    /// Keccak-f sub-blocks per slot: the key, the PRG blocks, then the sponge blocks.
    uint256 public immutable subsPerSlot;
    /// PRG blocks per slot.
    uint256 public immutable prgBlocks;
    /// PRG blocks per slot drawn for the input share.
    uint256 public immutable inBlocks;
    /// Head words any explicit row refers to.
    uint256 public immutable headWords;
    /// The hash chain of the stream.
    bytes32 public immutable rowsDigest;

    error Stream();
    error Discharge();

    constructor(
        uint256 kLog_,
        uint256 headSubs_,
        uint256 subsPerSlot_,
        uint256 prgBlocks_,
        uint256 inBlocks_,
        uint256 headWords_,
        bytes32 rowsDigest_
    ) {
        kLog = kLog_;
        headSubs = headSubs_;
        subsPerSlot = subsPerSlot_;
        prgBlocks = prgBlocks_;
        inBlocks = inBlocks_;
        headWords = headWords_;
        rowsDigest = rowsDigest_;
    }

    function claimWords() public view returns (uint256) {
        return 4 + 2 * (kLog - 6) + 64;
    }

    function keccakSubs() public view returns (uint256) {
        return 2 * subsPerSlot;
    }

    /// One claim's weights.
    struct Point {
        uint256 alpha;
        uint256 beta;
        uint256[] skip;
        uint256[] zp;
        uint256[] rowLo;
        uint256[] rowHi;
        uint256[] colLo;
        uint256[] colHi;
    }

    function _point(uint256[] calldata claims, uint256 i) internal view returns (Point memory pt) {
        uint256 rest = kLog - 6;
        uint256 cw = claimWords();
        uint256 b = i * cw;
        pt.alpha = claims[b];
        pt.beta = claims[b + 1];
        pt.skip = Piop.lagrange(Constants.PHI8, claims[b + 2]);
        pt.rowLo = GF2.eqTable(_slice(claims, b + 4, LO));
        pt.rowHi = GF2.eqTable(_slice(claims, b + 4 + LO, rest - LO));
        pt.colLo = GF2.eqTable(_slice(claims, b + 4 + rest, LO));
        pt.colHi = GF2.eqTable(_slice(claims, b + 4 + rest + LO, rest - LO));
        pt.zp = _slice(claims, b + cw - 64, 64);
    }

    function _slice(uint256[] calldata v, uint256 from, uint256 len) internal pure returns (uint256[] memory out) {
        out = new uint256[](len);
        for (uint256 k = 0; k < len; ++k) {
            out[k] = v[from + k];
        }
    }

    function _at(uint256 p, uint256 i) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := mload(add(p, shl(5, i)))
        }
    }

    function _data(uint256[] memory v) internal pure returns (uint256 p) {
        assembly ("memory-safe") {
            p := add(v, 0x20)
        }
    }

    // ---------------------------------------------------------------------------------------
    // The Keccak-f sub-blocks.
    // ---------------------------------------------------------------------------------------

    /// The Keccak-f sub-blocks' share of every claim's combination, 64 words per claim, with the
    /// constant-wire pin included.
    function keccakPart(uint256[] calldata claims) external returns (uint256[] memory out) {
        uint256 n = claims.length / claimWords();
        out = new uint256[](64 * n);
        uint256[] memory pre = _preimages();
        Fold memory f = _foldWork();
        uint256 subs = keccakSubs();
        for (uint256 i = 0; i < n; ++i) {
            Point memory pt = _point(claims, i);
            uint256[] memory part = new uint256[](64);
            uint256 konst = _fold(pt, part, pre, f);
            uint256 weight;
            uint256 weightKonst;
            for (uint256 j = headSubs; j < headSubs + subs; ++j) {
                weight ^= GF2.mul(pt.rowHi[j], pt.colHi[j]);
                weightKonst ^= pt.rowHi[j];
            }
            for (uint256 s = 0; s < 64; ++s) {
                out[64 * i + s] = GF2.mul(weight, part[s]);
            }
            out[64 * i] ^= GF2.mul(GF2.mul(weightKonst, konst) ^ pt.beta, GF2.mul(pt.colLo[0], pt.colHi[0]));
        }
        Meter.mark(200);
    }

    function _preimages() internal pure returns (uint256[] memory pre) {
        pre = new uint256[](1600);
        bytes memory rho = Constants.RHO;
        assembly ("memory-safe") {
            function idx(x, y, z) -> s {
                s := add(add(x, mul(5, y)), mul(25, z))
            }
            let base := add(pre, 0x20)
            let rhoAt := add(rho, 0x20)
            for { let s := 0 } lt(s, 1600) { s := add(s, 1) } {
                let lane := mod(s, 25)
                let x := mod(lane, 5)
                let y := div(lane, 5)
                let z := div(s, 25)
                let a := mod(add(x, mul(3, y)), 5)
                let r := byte(0, mload(add(rhoAt, add(mul(5, a), x))))
                let c := mod(sub(add(z, 64), r), 64)
                let cPrev := mod(add(c, 63), 64)
                let aMinus := mod(add(a, 4), 5)
                let aPlus := mod(add(a, 1), 5)
                let packed := idx(a, x, c)
                for { let yp := 0 } lt(yp, 5) { yp := add(yp, 1) } {
                    packed := or(packed, shl(mul(11, add(1, yp)), idx(aMinus, yp, c)))
                    packed := or(packed, shl(mul(11, add(6, yp)), idx(aPlus, yp, cPrev)))
                }
                mstore(add(base, shl(5, s)), packed)
            }
        }
    }

    /// `out = add + φᵀ(v)`.
    function _phiT(uint256[] memory v, uint256[] memory add_, uint256[] memory pre, uint256[] memory out) internal pure {
        assembly ("memory-safe") {
            let o := add(out, 0x20)
            let src := add(v, 0x20)
            let p := add(pre, 0x20)
            mcopy(o, add(add_, 0x20), mul(1600, 0x20))
            for { let s := 0 } lt(s, 1600) { s := add(s, 1) } {
                let val := mload(add(src, shl(5, s)))
                let packed := mload(add(p, shl(5, s)))
                for { let k := 0 } lt(k, 11) { k := add(k, 1) } {
                    let slot := add(o, shl(5, and(shr(mul(11, k), packed), 0x7ff)))
                    mstore(slot, xor(mload(slot), val))
                }
            }
        }
    }

    function _lanePos(uint256 j) internal pure returns (uint256) {
        return 64 * (j % 25) + j / 25;
    }

    /// The row weight at local position `p` of a sub-block, up to the sub-block's own weight.
    function _e(Point memory pt, uint256 p) internal pure returns (uint256) {
        return GF2.mul(pt.skip[p & 63], pt.rowLo[p >> 6]);
    }

    /// The χ rows of round `r`: their A-side and B-side column weights into `ca`, `cb`, the sum
    /// of their row weights, and those weights on the round's constant state.
    function _chi(Point memory pt, uint256 r, uint256[] memory pre, uint256[] memory ca, uint256[] memory cb)
        internal
        pure
        returns (uint256 sum, uint256 rcA, uint256 rcB)
    {
        assembly ("memory-safe") {
            let a := add(ca, 0x20)
            let b := add(cb, 0x20)
            for { let k := 0 } lt(k, mul(1600, 0x20)) { k := add(k, 0x20) } {
                mstore(add(a, k), 0)
                mstore(add(b, k), 0)
            }
        }
        for (uint256 s = 0; s < 1600; ++s) {
            uint256 x = (s % 25) % 5;
            uint256 base = s - x;
            uint256 e = _e(pt, T_BASE + r * 1600 + _lanePos(s));
            sum ^= e;
            _scatter(ca, pre[base + (x + 1) % 5], e);
            _scatter(cb, pre[base + (x + 2) % 5], e);
        }
        bytes memory masks = Constants.RC_MASKS;
        for (uint256 l = 0; l < 25; ++l) {
            uint256 m = _mask(masks, r, l);
            for (uint256 z = 0; m != 0; ++z) {
                if (m & 1 == 1) {
                    rcA ^= ca[l + 25 * z];
                    rcB ^= cb[l + 25 * z];
                }
                m >>= 1;
            }
        }
    }

    function _mask(bytes memory masks, uint256 r, uint256 l) internal pure returns (uint256 m) {
        assembly ("memory-safe") {
            m := shr(192, mload(add(add(masks, 0x20), mul(8, add(mul(25, r), l)))))
        }
    }

    function _scatter(uint256[] memory v, uint256 packed, uint256 e) internal pure {
        assembly ("memory-safe") {
            let base := add(v, 0x20)
            for { let k := 0 } lt(k, 11) { k := add(k, 1) } {
                let slot := add(base, shl(5, and(shr(mul(11, k), packed), 0x7ff)))
                mstore(slot, xor(mload(slot), e))
            }
        }
    }

    /// The backward pass's buffers and running sums.
    struct Fold {
        uint256[] kA;
        uint256[] kB;
        uint256[] nA;
        uint256[] nB;
        uint256[] ca;
        uint256[] cb;
        uint256[] pin;
        uint256 sumT;
        uint256 rcA;
        uint256 rcB;
        uint256 alphaTab;
    }

    function _foldWork() internal pure returns (Fold memory f) {
        f.alphaTab = Tables.region();
        f.kA = new uint256[](1600);
        f.kB = new uint256[](1600);
        f.nA = new uint256[](1600);
        f.nB = new uint256[](1600);
        f.ca = new uint256[](1600);
        f.cb = new uint256[](1600);
        f.pin = new uint256[](1600);
    }

    /// The shared fold of a Keccak-f sub-block, contracted against the column weights of its
    /// low bits into `out` by slot; returns the part landing on the constant wire.
    function _fold(Point memory pt, uint256[] memory out, uint256[] memory pre, Fold memory f)
        internal
        pure
        returns (uint256 konst)
    {
        Tables.buildMul(f.alphaTab, pt.alpha);
        (uint256 pinSum, uint256 rcPin) = _pins(pt, out, f);
        (f.sumT, f.rcA, f.rcB) = _chi(pt, 23, pre, f.ca, f.kB);
        _phiT(f.pin, f.ca, pre, f.kA);
        for (uint256 r = 23; r >= 1; --r) {
            _round(pt, out, pre, f, r);
        }
        _emitRow(pt, out, f, 0);
        konst = pinSum ^ Tables.lookup(f.alphaTab, f.sumT ^ f.rcA ^ rcPin) ^ f.rcB;
    }

    function _pins(Point memory pt, uint256[] memory out, Fold memory f) internal pure returns (uint256 sum, uint256 rcPin) {
        uint256[] memory pin = f.pin;
        for (uint256 j = 0; j < 1600; ++j) {
            uint256 e = _e(pt, STATE24_BASE + _lanePos(j));
            pin[j] = e;
            sum ^= e;
            uint256 p = T_BASE + 23 * 1600 + _lanePos(j);
            out[p & 63] ^= GF2.mul(pt.colLo[p >> 6], Tables.lookup(f.alphaTab, e));
        }
        bytes memory masks = Constants.RC_MASKS;
        for (uint256 l = 0; l < 25; ++l) {
            uint256 m = _mask(masks, 24, l);
            for (uint256 z = 0; m != 0; ++z) {
                if (m & 1 == 1) rcPin ^= pin[l + 25 * z];
                m >>= 1;
            }
        }
    }

    function _emitRow(Point memory pt, uint256[] memory out, Fold memory f, uint256 r) internal pure {
        uint256 base = r == 0 ? 0 : T_BASE + (r - 1) * 1600;
        for (uint256 s = 0; s < 1600; ++s) {
            uint256 p = base + _lanePos(s);
            uint256 v = Tables.lookup(f.alphaTab, f.kA[s]) ^ f.kB[s];
            out[p & 63] ^= GF2.mul(pt.colLo[p >> 6], v);
        }
    }

    function _round(Point memory pt, uint256[] memory out, uint256[] memory pre, Fold memory f, uint256 r)
        internal
        pure
    {
        _emitRow(pt, out, f, r);
        (uint256 sum, uint256 ra, uint256 rb) = _chi(pt, r - 1, pre, f.ca, f.cb);
        f.sumT ^= sum;
        f.rcA ^= ra;
        f.rcB ^= rb;
        _phiT(f.kA, f.ca, pre, f.nA);
        _phiT(f.kB, f.cb, pre, f.nB);
        (f.kA, f.nA) = (f.nA, f.kA);
        (f.kB, f.nB) = (f.nB, f.kB);
    }

    // ---------------------------------------------------------------------------------------
    // The stream.
    // ---------------------------------------------------------------------------------------

    /// One claim's accumulators and lookup tables over the stream.
    struct Ctx {
        uint256 f;
        uint256 konst;
        uint256 skip;
        uint256 zpTab;
        uint256 alphaTab;
        uint256 rHead;
        uint256 cHead;
        uint256 cTape;
        uint256 rSponge;
        uint256 rowLo;
        uint256 rowHi;
        uint256 colLo;
        uint256 colHi;
        uint256 slotA;
        uint256 slotB;
        uint256 eTilde;
        uint256 zs;
        uint256 skipSum;
    }

    /// Builds one claim's stream context, carrying the accumulators `f` and `konst` over.
    function _context(Point memory pt, uint256 f, uint256 konst) internal view returns (Ctx memory c) {
        c.f = f;
        c.konst = konst;
        c.skip = _data(pt.skip);
        c.rowLo = _data(pt.rowLo);
        c.rowHi = _data(pt.rowHi);
        c.colLo = _data(pt.colLo);
        c.colHi = _data(pt.colHi);
        c.slotA = _data(new uint256[](64));
        c.slotB = _data(new uint256[](64));
        assembly ("memory-safe") {
            let tab := mload(0x40)
            mstore(0x40, add(tab, mul(64, TAB)))
            mstore(add(c, 0x60), tab)
        }
        for (uint256 t = 0; t < 64; ++t) {
            Tables.buildMul(c.zpTab + t * TAB, pt.zp[t]);
            c.zs ^= GF2.mul(pt.zp[t], pt.skip[t]);
            c.skipSum ^= pt.skip[t];
        }
        c.alphaTab = Tables.region();
        Tables.buildMul(c.alphaTab, pt.alpha);
        c.rHead = _product(pt.rowLo, pt.rowHi, headWords);
        c.cHead = _product(pt.colLo, pt.colHi, headWords);
        c.cTape = _tape(pt);
        c.rSponge = _spongeRows(pt);
        uint256[] memory et = new uint256[](1600);
        for (uint256 p = 0; p < 1600; ++p) {
            et[p] = _e(pt, p);
        }
        c.eTilde = _data(et);
    }

    /// `lo[w & 1023]·hi[w >> 10]` for every word `w` below `n`.
    function _product(uint256[] memory lo, uint256[] memory hi, uint256 n) internal pure returns (uint256) {
        uint256[] memory t = new uint256[](n);
        for (uint256 w = 0; w < n; ++w) {
            t[w] = GF2.mul(lo[w & 1023], hi[w >> LO]);
        }
        return _data(t);
    }

    /// Column weights of the output-state words `32..36` of every Keccak-f sub-block.
    function _tape(Point memory pt) internal view returns (uint256) {
        uint256 subs = keccakSubs();
        uint256[] memory tape = new uint256[](4 * subs);
        for (uint256 j = 0; j < subs; ++j) {
            uint256 hi = pt.colHi[headSubs + j];
            for (uint256 k = 0; k < 4; ++k) {
                tape[4 * j + k] = GF2.mul(pt.colLo[32 + k], hi);
            }
        }
        return _data(tape);
    }

    /// Row weights of the input-state words `0..17` of every sponge sub-block.
    function _spongeRows(Point memory pt) internal view returns (uint256) {
        uint256 sponges = subsPerSlot - 1 - prgBlocks;
        uint256[] memory rs = new uint256[](2 * sponges * 17);
        for (uint256 s = 0; s < 2; ++s) {
            for (uint256 b = 0; b < sponges; ++b) {
                uint256 hi = pt.rowHi[headSubs + s * subsPerSlot + 1 + prgBlocks + b];
                for (uint256 k = 0; k < 17; ++k) {
                    rs[(s * sponges + b) * 17 + k] = GF2.mul(pt.rowLo[k], hi);
                }
            }
        }
        return _data(rs);
    }

    /// Folds one segment of the stream into the per-claim state `state` (for each claim, the
    /// scalar `Σ_t zp[t]·(α·A[t] + B[t])` so far, then the constant-wire weight so far) and
    /// extends the hash chain `chain` over it.
    function rows(uint256[] calldata claims, uint256[] calldata state, bytes32 chain, bytes calldata segment)
        external
        returns (uint256[] memory out, bytes32 chainOut)
    {
        uint256 n = claims.length / claimWords();
        uint256 at;
        uint256 len = segment.length;
        assembly ("memory-safe") {
            at := segment.offset
        }
        {
            uint256 hashed;
            assembly ("memory-safe") {
                let buf := mload(0x40)
                calldatacopy(buf, at, len)
                hashed := keccak256(buf, len)
            }
            chainOut = keccak256(abi.encodePacked(chain, hashed));
        }
        Ctx[] memory ctx = new Ctx[](n);
        for (uint256 i = 0; i < n; ++i) {
            ctx[i] = _context(_point(claims, i), state[2 * i], state[2 * i + 1]);
        }
        Meter.mark(202);
        _records(ctx, at, at + len);
        out = new uint256[](2 * n);
        for (uint256 i = 0; i < n; ++i) {
            out[2 * i] = ctx[i].f;
            out[2 * i + 1] = ctx[i].konst;
        }
        Meter.mark(201);
    }

    function _records(Ctx[] memory ctx, uint256 at, uint256 end) internal view {
        while (at < end) {
            uint256 tag = _byteAt(at);
            if (tag == 0) {
                at = _rowRecord(ctx, at + 1);
            } else if (tag == 1) {
                _identity(ctx, at + 1);
                at += 9;
            } else if (tag == 2) {
                _prg(ctx, _byteAt(at + 1));
                at += 2;
            } else if (tag == 3) {
                _sponge(ctx, _byteAt(at + 1));
                at += 2;
            } else {
                revert Stream();
            }
        }
        if (at != end) revert Stream();
    }

    function _byteAt(uint256 at) internal pure returns (uint256 b) {
        assembly ("memory-safe") {
            b := byte(0, calldataload(at))
        }
    }

    function _colAt(uint256 at) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := shr(224, calldataload(at))
        }
    }

    /// One explicit row, for every claim.
    function _rowRecord(Ctx[] memory ctx, uint256 at) internal view returns (uint256 next) {
        uint256 col;
        uint256 na;
        uint256 nb;
        assembly ("memory-safe") {
            let w := calldataload(at)
            col := shr(224, w)
            na := and(shr(208, w), 0xffff)
            nb := and(shr(192, w), 0xffff)
        }
        next = at + 8 + 4 * (na + nb);
        bool konstRow = nb == 1 && _colAt(at + 8 + 4 * na) == 0;
        for (uint256 i = 0; i < ctx.length; ++i) {
            Ctx memory c = ctx[i];
            uint256 e = GF2.mul(_at(c.skip, col & 63), _rowWeight(c, col));
            uint256 d = Tables.lookup(c.alphaTab, _gather(c, c.slotA, at + 8, na));
            if (konstRow) {
                c.konst ^= e;
            } else if (nb > 0) {
                d ^= _gather(c, c.slotB, at + 8 + 4 * na, nb);
            }
            c.f ^= GF2.mul(e, d);
        }
    }

    function _rowWeight(Ctx memory c, uint256 col) internal view returns (uint256) {
        uint256 w = col >> 6;
        if (w < headWords) return _at(c.rHead, w);
        uint256 lo = w & 1023;
        uint256 rel = (col >> 16) - headSubs;
        uint256 within = rel % subsPerSlot;
        if (within > prgBlocks && lo < 17) {
            uint256 sponges = subsPerSlot - 1 - prgBlocks;
            return _at(c.rSponge, ((rel / subsPerSlot) * sponges + within - 1 - prgBlocks) * 17 + lo);
        }
        return GF2.mul(_at(c.rowLo, lo), _at(c.rowHi, col >> 16));
    }

    function _colWeight(Ctx memory c, uint256 col) internal view returns (uint256) {
        uint256 w = col >> 6;
        if (w < headWords) return _at(c.cHead, w);
        uint256 lo = w & 1023;
        uint256 sub = col >> 16;
        if (sub >= headSubs && lo >= 32 && lo < 36) {
            return _at(c.cTape, (sub - headSubs) * 4 + lo - 32);
        }
        return GF2.mul(_at(c.colLo, lo), _at(c.colHi, sub));
    }

    /// `Σ_t zp[t]·S[t]` over the slot sums `S` of `count` columns at `at`, using `slots` as
    /// scratch.
    function _gather(Ctx memory c, uint256 slots, uint256 at, uint256 count) internal view returns (uint256 d) {
        uint256 touched;
        for (uint256 k = 0; k < count; ++k) {
            uint256 col = _colAt(at + 4 * k);
            uint256 v = _colWeight(c, col);
            uint256 t = col & 63;
            assembly ("memory-safe") {
                let slot := add(slots, shl(5, t))
                mstore(slot, xor(mload(slot), v))
            }
            touched |= 1 << t;
        }
        uint256 zpTab = c.zpTab;
        for (uint256 t = 0; touched != 0; ++t) {
            if (touched & 1 == 1) {
                uint256 v;
                assembly ("memory-safe") {
                    let slot := add(slots, shl(5, t))
                    v := mload(slot)
                    mstore(slot, 0)
                }
                d ^= Tables.lookup(zpTab + t * TAB, v);
            }
            touched >>= 1;
        }
    }

    /// Words `[w0, w1)` of identity rows, for every claim.
    function _identity(Ctx[] memory ctx, uint256 at) internal pure {
        uint256 w0;
        uint256 w1;
        assembly ("memory-safe") {
            let x := calldataload(at)
            w0 := shr(224, x)
            w1 := and(shr(192, x), 0xffffffff)
        }
        for (uint256 i = 0; i < ctx.length; ++i) {
            Ctx memory c = ctx[i];
            uint256 x;
            uint256 sr;
            for (uint256 w = w0; w < w1; ++w) {
                uint256 r = _at(c.rHead, w);
                x ^= GF2.mul(r, _at(c.cHead, w));
                sr ^= r;
            }
            c.f ^= GF2.mul(Tables.lookup(c.alphaTab, x), c.zs);
            c.konst ^= GF2.mul(sr, c.skipSum);
        }
    }

    /// Over local positions `[from, to)`: the sum of the row weights, and
    /// `Σ_p zp[(p − from) mod 64]·Ẽ(p)·colLo[32 + ((p − from) >> 6)]`, the weights of the rows
    /// linking position `p` to output-state position `p − from` of another sub-block.
    function _sums(Ctx memory c, uint256 from, uint256 to) internal pure returns (uint256 plain, uint256 linked) {
        for (uint256 p = from; p < to; ++p) {
            uint256 e = _at(c.eTilde, p);
            plain ^= e;
            uint256 q = p - from;
            linked ^= Tables.lookup(c.zpTab + (q & 63) * TAB, GF2.mul(e, _at(c.colLo, 32 + (q >> 6))));
        }
    }

    function _zpAt(Ctx memory c, uint256 t) internal pure returns (uint256) {
        return Tables.lookup(c.zpTab + t * TAB, 1);
    }

    /// `Σ Ẽ(p)` over the set bits `p` of the PRG tag.
    function _tagSum(Ctx memory c) internal pure returns (uint256 s) {
        bytes9 tag = "ZKBOO-PRG";
        for (uint256 p = 0; p < 72; ++p) {
            if ((uint8(tag[p / 8]) >> (p % 8)) & 1 == 1) s ^= _at(c.eTilde, p);
        }
    }

    /// All the PRG link rows of `slot`, for every claim.
    function _prg(Ctx[] memory ctx, uint256 slot) internal view {
        uint256 bits;
        while ((1 << bits) < prgBlocks) ++bits;
        for (uint256 i = 0; i < ctx.length; ++i) {
            _prgFor(ctx[i], slot, bits);
        }
    }

    function _prgFor(Ctx memory c, uint256 slot, uint256 bits) internal view {
        uint256 first = headSubs + slot * subsPerSlot + 1;
        (uint256 h, uint256[] memory g, uint256[] memory k) = _counterSums(c, first, bits);
        (uint256 all,) = _sums(c, 0, 1600);
        c.konst ^= GF2.mul(h, all);
        uint256 acc = _counterPart(c, slot, h, g, k);
        (, uint256 keyed) = _sums(c, 72, 328);
        acc ^= GF2.mul(GF2.mul(h, _at(c.colHi, first - 1)), keyed);
        c.f ^= Tables.lookup(c.alphaTab, acc);
    }

    /// The constant-wire and selector columns of the PRG link rows, weighted by `zp`.
    function _counterPart(Ctx memory c, uint256 slot, uint256 h, uint256[] memory g, uint256[] memory k)
        internal
        pure
        returns (uint256 acc)
    {
        uint256 constA = GF2.mul(h, _tagSum(c) ^ _at(c.eTilde, PRG_BITS) ^ _at(c.eTilde, 1087));
        uint256 sel;
        for (uint256 q = 0; q < g.length; ++q) {
            uint256 eq = _at(c.eTilde, 328 + q);
            constA ^= GF2.mul(g[q], eq);
            sel ^= GF2.mul(k[q], eq);
        }
        uint256 hi0 = _at(c.colHi, 0);
        uint256 z0 = _zpAt(c, 0);
        acc = GF2.mul(GF2.mul(GF2.mul(_at(c.colLo, 0), hi0), constA), z0);
        acc ^= GF2.mul(GF2.mul(GF2.mul(_at(c.colLo, 32), hi0), sel), z0 ^ _zpAt(c, 1 + slot));
    }

    /// The sum of the PRG sub-blocks' row weights, and per counter bit `q` the sums over the
    /// blocks whose counter has bit `q` set and over those whose selector touches bit `q`.
    function _counterSums(Ctx memory c, uint256 first, uint256 bits)
        internal
        view
        returns (uint256 h, uint256[] memory g, uint256[] memory k)
    {
        g = new uint256[](bits);
        k = new uint256[](bits);
        for (uint256 i = 0; i < prgBlocks; ++i) {
            uint256 r = _at(c.rowHi, first + i);
            h ^= r;
            uint256 cbits = i < inBlocks ? i : i - inBlocks;
            uint256 diff = i < inBlocks ? 0 : (cbits ^ (cbits + inBlocks));
            for (uint256 q = 0; q < bits; ++q) {
                if ((cbits >> q) & 1 == 1) g[q] ^= r;
                if ((diff >> q) & 1 == 1) k[q] ^= r;
            }
        }
    }

    /// The constant-wire B side and the permutation links of all the sponge rows of `slot`, for
    /// every claim.
    function _sponge(Ctx[] memory ctx, uint256 slot) internal view {
        uint256 first = headSubs + slot * subsPerSlot + 1 + prgBlocks;
        uint256 sponges = subsPerSlot - 1 - prgBlocks;
        for (uint256 i = 0; i < ctx.length; ++i) {
            Ctx memory c = ctx[i];
            uint256 hs = _at(c.rowHi, first);
            uint256 y;
            for (uint256 b = 1; b < sponges; ++b) {
                uint256 r = _at(c.rowHi, first + b);
                hs ^= r;
                y ^= GF2.mul(r, _at(c.colHi, first + b - 1));
            }
            (uint256 all, uint256 linked) = _sums(c, 0, 1600);
            c.konst ^= GF2.mul(hs, all);
            c.f ^= Tables.lookup(c.alphaTab, GF2.mul(y, linked));
        }
    }

    /// Checks that the stream was the pinned one and that every claim's equation closes.
    function finish(uint256[] calldata claims, uint256[] calldata part, uint256[] calldata state, bytes32 chain)
        external
        view
        returns (bool)
    {
        if (chain != rowsDigest) revert Stream();
        uint256 n = claims.length / claimWords();
        for (uint256 i = 0; i < n; ++i) {
            if (_closing(claims, part, state, i) != claims[i * claimWords() + 3]) revert Discharge();
        }
        return true;
    }

    function _closing(uint256[] calldata claims, uint256[] calldata part, uint256[] calldata state, uint256 i)
        internal
        view
        returns (uint256 sum)
    {
        Point memory pt = _point(claims, i);
        for (uint256 s = 0; s < 64; ++s) {
            sum ^= GF2.mul(part[64 * i + s], pt.zp[s]);
        }
        uint256 c0 = GF2.mul(pt.colLo[0], pt.colHi[0]);
        sum ^= state[2 * i] ^ GF2.mul(GF2.mul(state[2 * i + 1], c0), pt.zp[0]);
    }
}
