// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "../Calldata.sol";
import {Constants} from "../Constants.sol";
import {GF2} from "../GF2.sol";
import {Opening} from "../Opening.sol";
import {Piop} from "../Piop.sol";
import {Transcript} from "../Transcript.sol";
import {Config} from "./Config.sol";
import {IStage, Staged, State} from "./Staged.sol";
import {Walk} from "./Walk.sol";

/// The stages of a batched opening up to its residuals: the ring switches and Ligerito's first
/// messages, each level's opened rows in query ranges, the messages between levels, and the
/// out-of-domain residual (see `Opening`).
contract OpeningStages is IStage {
    error RingSwitchClaim();
    error MerklePath();
    error Shape();

    /// The call's first data byte, and the proof position it stands for.
    struct At {
        uint256 p;
        uint256 p0;
        uint256 pos0;
        uint256 tr;
    }

    function run(bytes calldata state, uint256 upto, bytes calldata data)
        external
        view
        returns (bytes memory, uint256[] memory)
    {
        State memory st = Staged.load(state, Staged.SWITCH, Staged.OOD);
        uint256 stage = st.v[Staged.STAGE];
        At memory at = At(Staged.offset(data), Staged.offset(data), st.v[Staged.POS], 0);
        uint256[] memory streams;
        if (stage == Staged.OPEN) {
            streams = _open(st, upto, at.p, data.length);
        } else if (stage == Staged.OOD) {
            _ood(st);
        } else {
            at.tr = Staged.restore(st.tr);
            if (stage == Staged.SWITCH) {
                _switch(st, at);
            } else if (stage == Staged.LEVEL) {
                _level(st, at);
            } else {
                _finish(st, at);
            }
            st.tr = Staged.keep(at.tr);
            if (st.v[Staged.STAGE] == Staged.OPEN) {
                streams = _openStreams(st);
            }
        }
        return (Staged.save(st), Staged.request(st, streams));
    }

    function _openStreams(State memory st) private pure returns (uint256[] memory) {
        return Staged.want2(
            Staged.want1(Staged.PROOF, st.v[Staged.ROWS_AT], 16 * st.v[Staged.WIDTH], 0),
            Staged.want1(Staged.PROOF, st.v[Staged.PATHS_AT], 32 * st.v[Staged.PATH_LEN], 0)
        );
    }

    function _switch(State memory st, At memory at) private pure {
        Transcript.label(at.tr, Constants.L_OPEN_0, Constants.L_OPEN_1, Constants.L_OPEN_LEN);
        uint256 n = st.v[Staged.NCLAIMS];
        uint256[] memory rdp = new uint256[](7 * n);
        uint256 target;
        uint256[] memory sums = new uint256[](n);
        for (uint256 c = 0; c < n; ++c) {
            sums[c] = _ringSwitch(at, st.a[Staged.CL_Z][c], st.a[Staged.CL_X + c], st.a[Staged.CL_VALUE][c], rdp, c);
            at.p += 128 * 16 + 8;
        }
        uint256[] memory gammas;
        if (n == 1) {
            gammas = Transcript.sampleVec(at.tr, 1);
        } else {
            gammas = Transcript.powSampleVec(at.tr, Calldata.nonce(at.p), 6, n);
            at.p += 8;
        }
        for (uint256 c = 0; c < n; ++c) {
            target ^= GF2.mul(gammas[c], sums[c]);
        }
        st.a[Staged.RDP] = rdp;
        st.a[Staged.GAMMAS] = gammas;
        st.v[Staged.TARGET] = target;
        _init(st, at);
    }

    function _ringSwitch(At memory at, uint256 z, uint256[] memory x, uint256 value, uint256[] memory rdp, uint256 c)
        private
        pure
        returns (uint256 sum)
    {
        uint256 tr = at.tr;
        uint256 p = at.p;
        Transcript.label(tr, Constants.L_RING_0, Constants.L_RING_1, Constants.L_RING_LEN);
        Transcript.observeSliceFromCalldata(tr, p, 128);
        if (Opening.claimCheck(Piop.lagrange(Constants.PHI8, z), x[0], p) != value) revert RingSwitchClaim();
        uint256[] memory r = Transcript.powSampleVec(tr, Calldata.nonce(p + 128 * 16), 3, 7);
        for (uint256 k = 0; k < 7; ++k) {
            rdp[7 * c + k] = r[k];
        }
        uint256[] memory table = Piop.bitTable(GF2.eqTable(r));
        for (uint256 i = 128; i > 0; --i) {
            uint256 l = Piop.applyTable(table, Calldata.f128(p + 16 * (i - 1)));
            sum = ((sum << 1) & GF2.M128) ^ ((sum >> 127) * 0x87) ^ l;
        }
    }

    function _init(State memory st, At memory at) private pure {
        uint256 logN = st.v[Staged.M] - 7;
        uint256 k0 = st.v[Staged.INITIAL_K];
        st.v[Staged.LOG_N] = logN;
        Transcript.label(at.tr, Constants.L_LIGERITO_0, Constants.L_LIGERITO_1, Constants.L_LIGERITO_LEN);
        Transcript.observe(at.tr, st.v[Staged.TARGET]);
        uint256[] memory cap = st.a[Staged.CAP];
        Transcript.header(at.tr, 5, 0, cap.length * 32);
        Staged.absorbWords(at.tr, cap);
        st.v[Staged.CLAIM] = st.v[Staged.TARGET];
        st.a[Staged.OOD_BETA] = new uint256[](Staged.MAX_OODS);
        st.a[Staged.OOD_SPLIT] = new uint256[](Staged.MAX_OODS);
        st.a[Staged.CONS_BETA] = new uint256[](Staged.MAX_LEVELS);
        st.a[Staged.CONS_COLS] = new uint256[](Staged.MAX_LEVELS);
        st.a[Staged.CONS_START] = new uint256[](Staged.MAX_LEVELS);
        _ood(st, at, 0, logN, type(uint256).max, false);
        (uint256 u0, uint256 u2) = _message(at);
        _fromMsg(st, u0, u2, st.v[Staged.CLAIM]);
        st.a[Staged.INITIAL] = _sumcheck(st, at, k0);
        st.v[Staged.SPLIT_DIM] = logN - k0 + 1;
        _readCap(st, at, Config.capDepth(st, 1));
        _ood(st, at, 1, st.v[Staged.SPLIT_DIM], 0, true);
        _queries(st, at, 0, 1 << (logN - k0 + st.a[Staged.CFG_RATES][0]));
        _setOpen(st, at, 0, 1 << k0, st.a[Staged.INITIAL]);
    }

    function _message(At memory at) private pure returns (uint256 u0, uint256 u2) {
        u0 = Calldata.f256(at.p);
        u2 = Calldata.f256(at.p + 32);
        Transcript.observeF256FromCalldata(at.tr, at.p);
        Transcript.observeF256FromCalldata(at.tr, at.p + 32);
        at.p += 64;
    }

    function _fromMsg(State memory st, uint256 u0, uint256 u2, uint256 claim) private pure {
        st.v[Staged.QC] = u0;
        st.v[Staged.QB] = claim ^ u2;
        st.v[Staged.QA] = u2;
    }

    function _evalQuad(State memory st, uint256 r) private pure returns (uint256) {
        return st.v[Staged.QC] ^ GF2.mul256(r, st.v[Staged.QB]) ^ GF2.mul256(GF2.mul256(r, r), st.v[Staged.QA]);
    }

    function _foldQuad(State memory st, uint256 u0, uint256 u2, uint256 claim, uint256 alpha) private pure {
        st.v[Staged.QC] ^= GF2.mul256By128(u0, alpha);
        st.v[Staged.QB] ^= GF2.mul256By128(claim ^ u2, alpha);
        st.v[Staged.QA] ^= GF2.mul256By128(u2, alpha);
    }

    function _sumcheck(State memory st, At memory at, uint256 k) private pure returns (uint256[] memory chs) {
        chs = new uint256[](k);
        for (uint256 j = 0; j < k; ++j) {
            uint256[] memory w = Transcript.sampleVec(at.tr, 2);
            uint256 ch = (w[1] << 128) | w[0];
            uint256 claim = _evalQuad(st, ch);
            st.v[Staged.CLAIM] = claim;
            chs[j] = ch;
            (uint256 u0, uint256 u2) = _message(at);
            _fromMsg(st, u0, u2, claim);
        }
    }

    function _readCap(State memory st, At memory at, uint256 depth) private pure {
        st.a[Staged.NEXT_CAP] = Staged.words(at.p, 1 << depth);
        Transcript.header(at.tr, 5, 0, 32 << depth);
        Transcript.bytesFromCalldata(at.tr, at.p, 32 << depth);
        at.p += 32 << depth;
    }

    function _ood(State memory st, At memory at, uint256 level, uint256 dim, uint256 split, bool intro) private pure {
        uint256 samples = st.a[Staged.CFG_OOD][level];
        for (uint256 j = 0; j < samples; ++j) {
            uint256[] memory point = Transcript.sampleVec(at.tr, dim);
            uint256 y = Calldata.f128(at.p);
            at.p += 16;
            Transcript.observe(at.tr, y);
            uint256 u0;
            uint256 u2;
            if (intro) {
                (u0, u2) = _message(at);
            }
            uint256 bits = st.a[Staged.CFG_CLAIM_BITS][intro ? level : 0];
            uint256 beta = Transcript.powSample(at.tr, Calldata.nonce(at.p), bits);
            at.p += 8;
            if (intro) {
                _foldQuad(st, u0, u2, y, beta);
            }
            st.v[Staged.CLAIM] ^= GF2.mul(beta, y);
            uint256 o = st.v[Staged.NOOD]++;
            st.a[Staged.OOD_POINT + o] = point;
            st.a[Staged.OOD_BETA][o] = beta;
            st.a[Staged.OOD_SPLIT][o] = split;
        }
    }

    /// Samples level `level`'s queries and batching point into the next consistency slot.
    function _queries(State memory st, At memory at, uint256 level, uint256 blockLen) private pure {
        uint256 count = st.a[Staged.CFG_QUERIES][level];
        uint256[] memory words = Transcript.powSampleVec(
            at.tr, Calldata.nonce(at.p), st.a[Staged.CFG_GRINDING][level], count
        );
        uint256[] memory alpha = Transcript.powSampleVec(
            at.tr, Calldata.nonce(at.p + 8), st.a[Staged.CFG_CONS_BITS][level], Opening.ceilLog2(count)
        );
        at.p += 16;
        uint256 d = st.a[Staged.CFG_BLOCK_LENS][level];
        if (blockLen != 1 << d) revert Shape();
        uint256[] memory qs = new uint256[](count);
        uint256[] memory depths = Config.depths(st, level);
        uint256 idx;
        for (uint256 i = 0; i < depths.length; ++i) {
            uint256 c = depths[i];
            uint256 lo = d - c;
            for (uint256 s = 0; s < (1 << c); ++s) {
                qs[idx] = (s << lo) | (words[idx] & ((1 << lo) - 1));
                ++idx;
            }
        }
        uint256 slot = st.v[Staged.NCONS];
        st.a[Staged.CONS_Q + slot] = qs;
        st.a[Staged.CONS_ALPHA + slot] = alpha;
    }

    /// Enters the opening of `level`'s rows, `width` values each, against the cap in `CAP`.
    function _setOpen(State memory st, At memory at, uint256 level, uint256 width, uint256[] memory lanes) private pure {
        uint256 c1 = Config.capDepth(st, level);
        if (st.a[Staged.CAP].length != 1 << c1) revert Shape();
        uint256 slot = st.v[Staged.NCONS];
        uint256 count = st.a[Staged.CONS_Q + slot].length;
        uint256 pathLen = st.a[Staged.CFG_BLOCK_LENS][level] - c1;
        st.v[Staged.LEVEL_I] = level;
        st.v[Staged.WIDTH] = width;
        st.v[Staged.PATH_LEN] = pathLen;
        st.a[Staged.LANES] = lanes;
        st.a[Staged.RW] = GF2.eqTable(st.a[Staged.CONS_ALPHA + slot]);
        st.a[Staged.COLS] = new uint256[](width);
        uint256 rowsAt = at.pos0 + (at.p - at.p0);
        st.v[Staged.ROWS_AT] = rowsAt;
        st.v[Staged.READ] = rowsAt;
        st.v[Staged.PATHS_AT] = rowsAt + count * width * 16;
        st.v[Staged.POS] = rowsAt + count * (width * 16 + pathLen * 32);
        Staged.enter(st, Staged.OPEN, count);
    }

    function _open(State memory st, uint256 upto, uint256 p, uint256 len) private view returns (uint256[] memory) {
        uint256 slot = st.v[Staged.NCONS];
        uint256[] memory qs = st.a[Staged.CONS_Q + slot];
        uint256 cursor = st.v[Staged.CURSOR];
        uint256 w = st.v[Staged.WIDTH];
        uint256 pl = st.v[Staged.PATH_LEN];
        if (upto <= cursor || upto > qs.length) revert Shape();
        uint256 k = upto - cursor;
        if (len < k * (16 * w + 32 * pl)) revert Shape();
        uint256 pathsAt = p + k * w * 16;
        uint256[] memory cap = st.a[Staged.CAP];
        for (uint256 i = 0; i < k; ++i) {
            uint256 q = qs[cursor + i];
            uint256 root = Opening.pathRoot(p + i * w * 16, w, pathsAt + i * pl * 32, pl, q);
            if (root != cap[q >> pl]) revert MerklePath();
        }
        _columnSums(st.a[Staged.COLS], st.a[Staged.RW], cursor, k, p, w);
        st.v[Staged.CURSOR] = upto;
        if (upto < qs.length) {
            return _openStreams(st);
        }
        return _openDone(st);
    }

    /// Batches the opened level's column sums into its enforced sum and leaves for the next stage.
    function _openDone(State memory st) private pure returns (uint256[] memory) {
        uint256[] memory lw = GF2.eqTable256(st.a[Staged.LANES]);
        uint256[] memory cols = st.a[Staged.COLS];
        uint256 enforced;
        for (uint256 l = 0; l < cols.length; ++l) {
            enforced ^= GF2.mul256By128(lw[l], cols[l]);
        }
        st.v[Staged.ENFORCED] = enforced;
        st.a[Staged.RW] = new uint256[](0);
        st.a[Staged.COLS] = new uint256[](0);
        st.a[Staged.LANES] = new uint256[](0);
        Staged.enter(st, st.v[Staged.FINAL] == 1 ? Staged.FINISH : Staged.LEVEL, 1);
        return Staged.sequential(st.v[Staged.POS]);
    }

    /// `cols[l] += Σ_i rw[from + i]·row_i[l]` over the `k` rows of `w` native values at `rowsAt`.
    function _columnSums(uint256[] memory cols, uint256[] memory rw, uint256 from, uint256 k, uint256 rowsAt, uint256 w)
        private
        pure
    {
        assembly ("memory-safe") {
            function native(x) -> v {
                v := or(and(shr(8, x), 0x00ff00ff00ff00ff00ff00ff00ff00ff), shl(8, and(x, 0x00ff00ff00ff00ff00ff00ff00ff00ff)))
                v := or(and(shr(16, v), 0x0000ffff0000ffff0000ffff0000ffff), shl(16, and(v, 0x0000ffff0000ffff0000ffff0000ffff)))
                v := or(and(shr(32, v), 0x00000000ffffffff00000000ffffffff), shl(32, and(v, 0x00000000ffffffff00000000ffffffff)))
                v := or(shr(64, v), shl(64, and(v, 0xffffffffffffffff)))
            }
            function red(v) -> o {
                let h := shr(128, v)
                o := xor(and(v, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
                h := shr(128, o)
                o := xor(and(o, 0xffffffffffffffffffffffffffffffff), xor(h, xor(shl(1, h), xor(shl(2, h), shl(7, h)))))
            }
            function horner(h, a) {
                mstore(h, 0)
                for { let i := 1 } lt(i, 256) { i := add(i, 1) } {
                    mstore(add(h, shl(5, i)), xor(shl(1, mload(add(h, shl(5, shr(1, i))))), mul(and(i, 1), a)))
                }
            }
            function hmul(h, y) -> o {
                o := mload(add(h, shl(5, byte(16, y))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(17, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(18, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(19, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(20, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(21, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(22, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(23, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(24, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(25, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(26, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(27, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(28, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(29, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(30, y)))))
                o := xor(shl(8, o), mload(add(h, shl(5, byte(31, y)))))
            }
            function row(h, cd, at, width) {
                for { let l := 0 } lt(l, width) { l := add(l, 1) } {
                    let slot := add(cd, shl(5, l))
                    let x := shr(128, calldataload(add(at, mul(16, l))))
                    mstore(slot, xor(mload(slot), red(hmul(h, native(x)))))
                }
            }
            let h := mload(0x40)
            let cd := add(cols, 0x20)
            let rd := add(rw, 0x20)
            for { let i := 0 } lt(i, k) { i := add(i, 1) } {
                horner(h, mload(add(rd, shl(5, add(from, i)))))
                row(h, cd, add(rowsAt, mul(i, mul(w, 16))), w)
            }
        }
    }

    function _level(State memory st, At memory at) private pure {
        uint256 level = st.v[Staged.LEVEL_I];
        _introduce(st, at, level);
        uint256 i = level;
        uint256[] memory chs = _sumcheck(st, at, st.a[Staged.CFG_KS][i]);
        st.a[Staged.LEVELS + i] = chs;
        uint256 ext = st.v[Staged.SPLIT_DIM] - st.a[Staged.CFG_KS][i];
        uint256 blockLen = 1 << (st.v[Staged.PREV_COLS] + st.v[Staged.PREV_RATE]);
        uint256 width = 1 << st.v[Staged.PREV_LANES];
        st.a[Staged.CAP] = st.a[Staged.NEXT_CAP];
        st.v[Staged.EXT] = ext;
        if (i + 1 == st.v[Staged.STEPS]) {
            uint256 n = 2 << ext;
            for (uint256 j = 0; j < n; ++j) {
                Transcript.observe(at.tr, Calldata.f128(at.p + 16 * j));
            }
            uint256[] memory mu = new uint256[](1 << ext);
            for (uint256 y = 0; y < mu.length; ++y) {
                mu[y] = (Calldata.f128(at.p + 32 * y + 16) << 128) | Calldata.f128(at.p + 32 * y);
            }
            st.a[Staged.MU] = mu;
            at.p += 32 << ext;
            st.v[Staged.FINAL] = 1;
        } else {
            st.v[Staged.SPLIT_DIM] = ext + 1;
            _readCap(st, at, Config.capDepth(st, i + 2));
            _ood(st, at, i + 2, ext + 1, i + 1, true);
        }
        _queries(st, at, i + 1, blockLen);
        _setOpen(st, at, i + 1, width, chs);
    }

    /// Folds the enforced sum of the level just opened into the running sumcheck.
    function _introduce(State memory st, At memory at, uint256 level) private pure {
        (uint256 u0, uint256 u2) = _message(at);
        uint256 beta = Transcript.powSample(at.tr, Calldata.nonce(at.p), st.a[Staged.CFG_CLAIM_BITS][level + 1]);
        at.p += 8;
        uint256 enforced = st.v[Staged.ENFORCED];
        _foldQuad(st, u0, u2, enforced, beta);
        st.v[Staged.CLAIM] ^= GF2.mul256By128(enforced, beta);
        uint256 slot = st.v[Staged.NCONS]++;
        st.a[Staged.CONS_BETA][slot] = beta;
        st.a[Staged.CONS_COLS][slot] =
            level == 0 ? st.v[Staged.LOG_N] - st.v[Staged.INITIAL_K] : st.v[Staged.EXT];
        st.a[Staged.CONS_START][slot] = level;
        st.v[Staged.PREV_LANES] = st.a[Staged.CFG_KS][level];
        st.v[Staged.PREV_COLS] = st.v[Staged.SPLIT_DIM] - st.v[Staged.PREV_LANES];
        st.v[Staged.PREV_RATE] = st.a[Staged.CFG_RATES][level + 1];
    }

    function _finish(State memory st, At memory at) private pure {
        uint256 level = st.v[Staged.LEVEL_I];
        uint256 beta = Transcript.powSample(at.tr, Calldata.nonce(at.p), st.a[Staged.CFG_CLAIM_BITS][level]);
        at.p += 8;
        st.v[Staged.CLAIM] ^= GF2.mul256By128(st.v[Staged.ENFORCED], beta);
        uint256 slot = st.v[Staged.NCONS]++;
        st.a[Staged.CONS_BETA][slot] = beta;
        st.a[Staged.CONS_COLS][slot] = st.v[Staged.EXT];
        st.a[Staged.CONS_START][slot] = st.v[Staged.STEPS];
        st.v[Staged.POS] = at.pos0 + (at.p - at.p0);
        st.v[Staged.READ] = st.v[Staged.POS];
        st.a[Staged.CAP] = new uint256[](0);
        st.a[Staged.NEXT_CAP] = new uint256[](0);
        Staged.enter(st, Staged.OOD, 1);
    }

    function _ood(State memory st) private pure {
        uint256[] memory original = Walk.originalChallenges(st, 0, true);
        st.v[Staged.GOT] = Walk.oodDot(st, original);
        uint256 n = st.v[Staged.NCLAIMS];
        uint256[] memory ng = new uint256[](n);
        uint256 items;
        uint256 pLen = original.length;
        uint256 points = 1 << st.v[Staged.EXT];
        for (uint256 c = 0; c < n; ++c) {
            uint256[] memory x = st.a[Staged.CL_X + c];
            for (uint256 i = 0; i < pLen; ++i) {
                if (x[1 + i] > 1) ++ng[c];
            }
            items += 1 + (ng[c] > 5 ? ng[c] - 5 : 0) + points;
        }
        st.a[Staged.RS_NG] = ng;
        Staged.enter(st, Staged.RS, items);
    }
}
