// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "./Constants.sol";
import {GF2} from "./GF2.sol";
import {Meter} from "./Meter.sol";
import {Piop} from "./Piop.sol";

/// The lincheck's matrix discharge for one statement's response block: the fold of the
/// Keccak-f sub-blocks, evaluated once and re-weighted, and the block's explicit rows, read from
/// a calldata stream whose hash chain must end at the statement's pinned digest.
///
/// A claim is `4 + 2·(kLog − 6) + 64` words: `alpha, beta, z, running`, the row point, the column
/// point, then the collapsed witness. The discharge of a lift is `keccakPart`, then `rows` over
/// every segment of the stream in order, then `finish`.
contract FlockDischarge {
    uint256 internal constant SUB_LOG = 16;
    uint256 internal constant LO = 10;
    uint256 internal constant STATE24_BASE = 2048;
    uint256 internal constant T_BASE = 4160;

    /// log2 of the block width.
    uint256 public immutable kLog;
    /// Sub-blocks before the first Keccak-f sub-block.
    uint256 public immutable headSubs;
    /// Keccak-f sub-blocks.
    uint256 public immutable keccakSubs;
    /// The hash chain of the explicit-row stream.
    bytes32 public immutable rowsDigest;

    error Stream();
    error Discharge();

    constructor(uint256 kLog_, uint256 headSubs_, uint256 keccakSubs_, bytes32 rowsDigest_) {
        kLog = kLog_;
        headSubs = headSubs_;
        keccakSubs = keccakSubs_;
        rowsDigest = rowsDigest_;
    }

    /// One claim's weights: the skip weights and the four `eq` tables of its row and column
    /// points, split at the sub-block's low bits.
    struct Point {
        uint256 alpha;
        uint256 beta;
        uint256 running;
        uint256[] skip;
        uint256[] rowLo;
        uint256[] rowHi;
        uint256[] colLo;
        uint256[] colHi;
    }

    function claimWords() public view returns (uint256) {
        return 4 + 2 * (kLog - 6) + 64;
    }

    function _point(uint256[] calldata claims, uint256 i) internal view returns (Point memory pt) {
        uint256 rest = kLog - 6;
        uint256 b = i * claimWords();
        pt.alpha = claims[b];
        pt.beta = claims[b + 1];
        pt.running = claims[b + 3];
        pt.skip = Piop.lagrange(Constants.PHI8, claims[b + 2]);
        pt.rowLo = GF2.eqTable(_slice(claims, b + 4, LO));
        pt.rowHi = GF2.eqTable(_slice(claims, b + 4 + LO, rest - LO));
        pt.colLo = GF2.eqTable(_slice(claims, b + 4 + rest, LO));
        pt.colHi = GF2.eqTable(_slice(claims, b + 4 + rest + LO, rest - LO));
    }

    function _slice(uint256[] calldata v, uint256 from, uint256 len) internal pure returns (uint256[] memory out) {
        out = new uint256[](len);
        for (uint256 k = 0; k < len; ++k) {
            out[k] = v[from + k];
        }
    }

    /// The Keccak-f sub-blocks' share of every claim's combination, 64 words per claim, with the
    /// constant-wire pin included.
    function keccakPart(uint256[] calldata claims) external returns (uint256[] memory out) {
        uint256 n = claims.length / claimWords();
        out = new uint256[](64 * n);
        uint256[] memory pre = _preimages();
        for (uint256 i = 0; i < n; ++i) {
            Point memory pt = _point(claims, i);
            uint256[] memory part = new uint256[](64);
            uint256 konst = _fold(pt, part, pre);
            uint256 weight;
            uint256 weightKonst;
            for (uint256 j = headSubs; j < headSubs + keccakSubs; ++j) {
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

    /// `pre[s]` packs the 11 input-state bits whose XOR is state bit `s` of `(π∘ρ∘θ)(state)`,
    /// eleven bits each.
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
                let b := x
                let r := byte(0, mload(add(rhoAt, add(mul(5, a), b))))
                let c := mod(sub(add(z, 64), r), 64)
                let cPrev := mod(add(c, 63), 64)
                let aMinus := mod(add(a, 4), 5)
                let aPlus := mod(add(a, 1), 5)
                let packed := idx(a, b, c)
                for { let yp := 0 } lt(yp, 5) { yp := add(yp, 1) } {
                    packed := or(packed, shl(mul(11, add(1, yp)), idx(aMinus, yp, c)))
                    packed := or(packed, shl(mul(11, add(6, yp)), idx(aPlus, yp, cPrev)))
                }
                mstore(add(base, shl(5, s)), packed)
            }
        }
    }

    /// `v ↦ out` with `out[s_in] = Σ_{s_out : s_in ∈ pre[s_out]} v[s_out]`, then `out += add`.
    function _phiT(uint256[] memory v, uint256[] memory add_, uint256[] memory pre) internal pure returns (uint256[] memory out) {
        out = new uint256[](1600);
        assembly ("memory-safe") {
            let o := add(out, 0x20)
            let src := add(v, 0x20)
            let p := add(pre, 0x20)
            for { let s := 0 } lt(s, 1600) { s := add(s, 1) } {
                let val := mload(add(src, shl(5, s)))
                let packed := mload(add(p, shl(5, s)))
                for { let k := 0 } lt(k, 11) { k := add(k, 1) } {
                    let slot := add(o, shl(5, and(shr(mul(11, k), packed), 0x7ff)))
                    mstore(slot, xor(mload(slot), val))
                }
            }
            let a := add(add_, 0x20)
            for { let s := 0 } lt(s, 1600) { s := add(s, 1) } {
                let slot := add(o, shl(5, s))
                mstore(slot, xor(mload(slot), mload(add(a, shl(5, s)))))
            }
        }
    }

    /// The local row weight at sub-block position `p`.
    function _e(Point memory pt, uint256 p) internal pure returns (uint256) {
        return GF2.mul(pt.skip[p & 63], pt.rowLo[p >> 6]);
    }

    function _lanePos(uint256 j) internal pure returns (uint256) {
        return 64 * (j % 25) + j / 25;
    }

    /// Accumulates `colLo[p >> 6]·v` into `out[p mod 64]`.
    function _emit(Point memory pt, uint256[] memory out, uint256 p, uint256 v) internal pure {
        out[p & 63] ^= GF2.mul(pt.colLo[p >> 6], v);
    }

    /// The χ rows of round `r`: their A-side and B-side column weights, the sum of their row
    /// weights, and those weights on the round's constant state.
    function _chi(Point memory pt, uint256 r, uint256[] memory pre)
        internal
        pure
        returns (uint256[] memory ca, uint256[] memory cb, uint256 sum, uint256 rcA, uint256 rcB)
    {
        ca = new uint256[](1600);
        cb = new uint256[](1600);
        for (uint256 s = 0; s < 1600; ++s) {
            uint256 lane = s % 25;
            uint256 x = lane % 5;
            uint256 y = lane / 5;
            uint256 z = s / 25;
            uint256 e = _e(pt, T_BASE + r * 1600 + _lanePos(s));
            sum ^= e;
            _scatter(ca, pre[((x + 1) % 5) + 5 * y + 25 * z], e);
            _scatter(cb, pre[((x + 2) % 5) + 5 * y + 25 * z], e);
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

    /// The backward pass of the shared fold.
    struct Fold {
        uint256[] kA;
        uint256[] kB;
        uint256 sumT;
        uint256 rcA;
        uint256 rcB;
    }

    /// The shared fold of a Keccak-f sub-block, contracted against the column weights of its
    /// low bits, returned in `out` by slot; the part landing on the constant wire is returned.
    function _fold(Point memory pt, uint256[] memory out, uint256[] memory pre) internal pure returns (uint256 konst) {
        (uint256[] memory pin, uint256 pinSum, uint256 rcPin) = _pins(pt, out);
        Fold memory f;
        uint256[] memory ca;
        (ca, f.kB, f.sumT, f.rcA, f.rcB) = _chi(pt, 23, pre);
        f.kA = _phiT(pin, ca, pre);
        for (uint256 r = 23; r >= 1; --r) {
            _round(pt, out, pre, f, r);
        }
        _emitRow(pt, out, f, 0);
        konst = pinSum ^ GF2.mul(pt.alpha, f.sumT) ^ GF2.mul(pt.alpha, f.rcA) ^ f.rcB ^ GF2.mul(pt.alpha, rcPin);
    }

    /// The output-state pins: their weights, emitted on the last χ output, their sum, and their
    /// weight on the final constant state.
    function _pins(Point memory pt, uint256[] memory out)
        internal
        pure
        returns (uint256[] memory pin, uint256 sum, uint256 rcPin)
    {
        pin = new uint256[](1600);
        for (uint256 j = 0; j < 1600; ++j) {
            pin[j] = _e(pt, STATE24_BASE + _lanePos(j));
            sum ^= pin[j];
            _emit(pt, out, T_BASE + 23 * 1600 + _lanePos(j), GF2.mul(pt.alpha, pin[j]));
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

    /// Emits `α·kA + kB` on the χ output of round `r − 1`, or on the input state for `r = 0`.
    function _emitRow(Point memory pt, uint256[] memory out, Fold memory f, uint256 r) internal pure {
        uint256 base = r == 0 ? 0 : T_BASE + (r - 1) * 1600;
        for (uint256 s = 0; s < 1600; ++s) {
            _emit(pt, out, base + _lanePos(s), GF2.mul(pt.alpha, f.kA[s]) ^ f.kB[s]);
        }
    }

    /// One step of the backward pass, from round `r` to round `r − 1`.
    function _round(Point memory pt, uint256[] memory out, uint256[] memory pre, Fold memory f, uint256 r)
        internal
        pure
    {
        _emitRow(pt, out, f, r);
        (uint256[] memory na, uint256[] memory nb, uint256 sum, uint256 ra, uint256 rb) = _chi(pt, r - 1, pre);
        f.sumT ^= sum;
        f.rcA ^= ra;
        f.rcB ^= rb;
        f.kA = _phiT(f.kA, na, pre);
        f.kB = _phiT(f.kB, nb, pre);
    }

    /// Folds one segment of explicit rows into the accumulators `acc` (for each claim, 64 A-side
    /// then 64 B-side words) and extends the hash chain `chain` over it.
    ///
    /// A row is its column (four bytes), its A-side and B-side lengths (two bytes each), then its
    /// A-side and B-side columns (four bytes each), all big-endian.
    function rows(uint256[] calldata claims, uint256[] calldata acc, bytes32 chain, bytes calldata segment)
        external
        returns (uint256[] memory accOut, bytes32 chainOut)
    {
        uint256 n = claims.length / claimWords();
        accOut = acc;
        uint256 at;
        uint256 len = segment.length;
        assembly ("memory-safe") {
            at := segment.offset
        }
        uint256 hashed;
        {
            uint256 buf;
            assembly ("memory-safe") {
                buf := mload(0x40)
                calldatacopy(buf, at, len)
                hashed := keccak256(buf, len)
            }
        }
        chainOut = keccak256(abi.encodePacked(chain, hashed));
        for (uint256 i = 0; i < n; ++i) {
            Point memory pt = _point(claims, i);
            _segment(pt, accOut, 128 * i, at, at + len);
        }
        Meter.mark(201);
    }

    /// The running state of one claim over a segment.
    struct Seg {
        uint256[] acc;
        uint256 accBase;
        uint256[] slotA;
        uint256[] slotB;
        uint256 konst;
    }

    /// The explicit rows between calldata offsets `at` and `end`, for one claim.
    function _segment(Point memory pt, uint256[] memory acc, uint256 accBase, uint256 at, uint256 end) internal pure {
        Seg memory sg = Seg(acc, accBase, new uint256[](64), new uint256[](64), 0);
        while (at < end) {
            at = _row(pt, sg, at);
        }
        if (at != end) revert Stream();
        acc[accBase + 64] ^= GF2.mul(sg.konst, GF2.mul(pt.colLo[0], pt.colHi[0]));
    }

    /// Folds the row at `at` into the segment state and returns the offset after it.
    function _row(Point memory pt, Seg memory sg, uint256 at) internal pure returns (uint256) {
        uint256 col;
        uint256 na;
        uint256 nb;
        assembly ("memory-safe") {
            let w := calldataload(at)
            col := shr(224, w)
            na := and(shr(208, w), 0xffff)
            nb := and(shr(192, w), 0xffff)
        }
        uint256 e = GF2.mul(pt.skip[col & 63], _rowWeight(pt, col >> 6));
        at += 8;
        _flush(sg.acc, sg.accBase, sg.slotA, _gather(pt, sg.slotA, at, na), e);
        at += 4 * na;
        if (nb == 1 && _col(at) == 0) {
            sg.konst ^= e;
        } else {
            _flush(sg.acc, sg.accBase + 64, sg.slotB, _gather(pt, sg.slotB, at, nb), e);
        }
        return at + 4 * nb;
    }

    function _col(uint256 at) internal pure returns (uint256 c) {
        assembly ("memory-safe") {
            c := shr(224, calldataload(at))
        }
    }

    function _rowWeight(Point memory pt, uint256 word) internal pure returns (uint256) {
        return GF2.mul(pt.rowLo[word & 1023], pt.rowHi[word >> LO]);
    }

    /// Adds the column weights of `count` columns at `at` into `slots`, returning the slots touched.
    function _gather(Point memory pt, uint256[] memory slots, uint256 at, uint256 count)
        internal
        pure
        returns (uint256 touched)
    {
        for (uint256 k = 0; k < count; ++k) {
            uint256 c = _col(at + 4 * k);
            uint256 w = c >> 6;
            slots[c & 63] ^= GF2.mul(pt.colLo[w & 1023], pt.colHi[w >> LO]);
            touched |= 1 << (c & 63);
        }
    }

    /// Moves the touched slots into the accumulator, weighted by `e`, and clears them.
    function _flush(uint256[] memory acc, uint256 base, uint256[] memory slots, uint256 touched, uint256 e)
        internal
        pure
    {
        for (uint256 s = 0; touched != 0; ++s) {
            if (touched & 1 == 1) {
                acc[base + s] ^= GF2.mul(e, slots[s]);
                slots[s] = 0;
            }
            touched >>= 1;
        }
    }

    /// Checks that the stream was the pinned one and that every claim's equation closes.
    function finish(uint256[] calldata claims, uint256[] calldata part, uint256[] calldata acc, bytes32 chain)
        external
        view
        returns (bool)
    {
        if (chain != rowsDigest) revert Stream();
        uint256 n = claims.length / claimWords();
        for (uint256 i = 0; i < n; ++i) {
            if (_closing(claims, part, acc, i) != claims[i * claimWords() + 3]) revert Discharge();
        }
        return true;
    }

    function _closing(uint256[] calldata claims, uint256[] calldata part, uint256[] calldata acc, uint256 i)
        internal
        view
        returns (uint256 sum)
    {
        uint256 cw = claimWords();
        uint256 alpha = claims[i * cw];
        uint256 zAt = i * cw + cw - 64;
        for (uint256 s = 0; s < 64; ++s) {
            uint256 comb = part[64 * i + s] ^ GF2.mul(alpha, acc[128 * i + s]) ^ acc[128 * i + 64 + s];
            sum ^= GF2.mul(comb, claims[zAt + s]);
        }
    }
}
