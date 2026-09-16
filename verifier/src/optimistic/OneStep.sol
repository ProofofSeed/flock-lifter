// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {CodeStore} from "./CodeStore.sol";
import {Merkle} from "./Merkle.sol";

/// A program the machine runs: its bytecode held in chunks, its jump destinations, and the
/// address it runs as.
struct Program {
    address[] code;
    uint256 codeLen;
    address jumps;
    address self;
}

/// The committed state of the machine during one step, with the witness the step consumes.
struct Frame {
    uint256 kind;
    uint256 call;
    uint256 pc;
    uint256 msize;
    bytes32 memRoot;
    uint256[] stack;
    uint256 sp;
    bytes ret;
    uint256[8] cx;
    uint256 memAt;
    uint256 memEnd;
    uint256 cdAt;
    uint256 cdEnd;
    uint256 outsAt;
    uint256 outsEnd;
}

/// One step of the EVM executing the lift's verification: four calls in a fixed sequence, the
/// lift contract then the matrix discharge's Keccak part, stream and final check, each later
/// call's calldata built from earlier outputs. A state commits to the program counter, the
/// stack, memory as a Merkle tree, the return data, and the call's context, which commits to its
/// calldata as a prefix tree and a body tree and to the earlier outputs.
///
/// The machine is the EVM with three departures, all of which only ever turn a run into a
/// rejection or leave it unchanged: `GAS` pushes a constant, the only callable address is the
/// SHA-256 precompile, and any opcode outside the implemented set, any memory beyond
/// `2^MEM_DEPTH` words and any exceptional halt rejects.
contract OneStep {
    uint256 internal constant RUNNING = 0;
    uint256 internal constant ACCEPTED = 1;
    uint256 internal constant REJECTED = 2;
    uint256 internal constant CALLS = 4;
    uint256 internal constant MEM_DEPTH = 22;
    uint256 internal constant PREFIX_DEPTH = 10;
    uint256 internal constant BODY_DEPTH = 24;
    uint256 internal constant MAX_STACK = 1024;
    uint256 internal constant GAS_CONSTANT = 1 << 32;
    bytes4 internal constant KECCAK_PART = bytes4(keccak256("keccakPart(uint256[])"));
    bytes4 internal constant ROWS = bytes4(keccak256("rows(uint256[],uint256[],bytes32,bytes)"));
    bytes4 internal constant FINISH = bytes4(keccak256("finish(uint256[],uint256[],uint256[],bytes32)"));

    error Witness();
    error Output();

    Program internal lift;
    Program internal discharge;
    /// The root of the discharge stream's word tree.
    bytes32 public immutable streamRoot;
    /// The discharge stream's length in bytes.
    uint256 public immutable streamLen;
    /// The caller every call runs under.
    address public immutable caller;
    /// The chain identifier every call sees.
    uint256 public immutable chainId;

    constructor(
        address[] memory liftCode,
        uint256 liftLen,
        address[] memory dischargeCode,
        uint256 dischargeLen,
        address liftSelf,
        address dischargeSelf,
        bytes32 streamRoot_,
        uint256 streamLen_,
        address caller_,
        uint256 chainId_
    ) {
        lift = Program(liftCode, liftLen, address(0), liftSelf);
        discharge = Program(dischargeCode, dischargeLen, address(0), dischargeSelf);
        streamRoot = streamRoot_;
        streamLen = streamLen_;
        caller = caller_;
        chainId = chainId_;
    }

    /// Builds the jump-destination bitmaps of both programs; one call each, `which` naming the
    /// program.
    function buildJumps(uint256 which) external {
        Program storage p = which == 0 ? lift : discharge;
        require(p.jumps == address(0), "built");
        p.jumps = CodeStore.buildJumps(p.code, p.codeLen);
    }

    /// Program `which`: the contracts holding its code, its length, its jump table and the
    /// address it runs as.
    function program(uint256 which) external view returns (address[] memory, uint256, address, address) {
        Program storage p = which == 0 ? lift : discharge;
        return (p.code, p.codeLen, p.jumps, p.self);
    }

    /// The Keccak-256 hash of program `which`'s code, to compare with the audited bytecode.
    function codeHash(uint256 which) external view returns (bytes32) {
        Program memory p = which == 0 ? lift : discharge;
        bytes memory code = new bytes(p.codeLen);
        uint256 at;
        assembly ("memory-safe") {
            at := add(code, 0x20)
        }
        CodeStore.read(p.code, 0, p.codeLen, at);
        return keccak256(code);
    }

    /// Whether both programs' bitmaps are built.
    function ready() external view returns (bool) {
        return lift.jumps != address(0) && discharge.jumps != address(0);
    }

    // ---------------------------------------------------------------- state hashing

    /// The hash of a terminal state.
    function terminal(uint256 kind) public pure returns (bytes32) {
        return keccak256(abi.encode(kind, 0, 0, 0, 0, 0, 0, 0));
    }

    /// The hash of a running state.
    function running(
        uint256 call,
        uint256 pc,
        uint256 msize,
        bytes32 memRoot,
        bytes32 ctx,
        bytes32 retHash,
        bytes32 stackHash
    ) public pure returns (bytes32) {
        return keccak256(abi.encode(RUNNING, call, pc, msize, memRoot, ctx, retHash, stackHash));
    }

    /// The commitment to a call's calldata.
    function calldataCommit(uint256 len, bytes4 selector, bytes32 prefixRoot, uint256 prefixWords, bytes32 bodyRoot)
        public
        pure
        returns (uint256[5] memory)
    {
        return [len, uint256(uint32(selector)), uint256(prefixRoot), prefixWords, uint256(bodyRoot)];
    }

    function _ctx(uint256[8] memory cx) internal pure returns (bytes32) {
        return keccak256(abi.encode(cx));
    }

    /// The state a call starts in.
    function start(uint256 call, uint256[8] memory cx) public pure returns (bytes32) {
        return running(call, 0, 0, Merkle.zero(MEM_DEPTH), _ctx(cx), keccak256(""), keccak256(""));
    }

    /// The first state of a verification of `proof` (committed as `proofRoot` over `proofLen`
    /// bytes) against the expected output `output`, its word counts `counts` and `binding`.
    function initial(bytes calldata output, uint256 counts, bytes calldata binding, bytes32 proofRoot, uint256 proofLen)
        external
        pure
        returns (bytes32)
    {
        uint256 ow = (output.length + 31) / 32;
        uint256 bw = (binding.length + 31) / 32;
        uint256 p = 4 + 1 + ow + 1 + bw + 1;
        uint256[] memory prefix = new uint256[](p);
        prefix[0] = 0x80;
        prefix[1] = counts;
        prefix[2] = 0x80 + 32 * (1 + ow);
        prefix[3] = prefix[2] + 32 * (1 + bw);
        prefix[4] = output.length;
        _packBytes(prefix, 5, output);
        prefix[5 + ow] = binding.length;
        _packBytes(prefix, 6 + ow, binding);
        prefix[p - 1] = proofLen;
        uint256[8] memory cx;
        cx[0] = 4 + 32 * p + 32 * ((proofLen + 31) / 32);
        cx[1] = uint32(bytes4(keccak256("verify(bytes,uint256,bytes,bytes)")));
        cx[2] = uint256(_treeRoot(prefix, PREFIX_DEPTH));
        cx[3] = p;
        cx[4] = uint256(proofRoot);
        return start(0, cx);
    }

    function _packBytes(uint256[] memory dst, uint256 at, bytes calldata src) internal pure {
        for (uint256 i = 0; i < src.length; ++i) {
            dst[at + i / 32] |= uint256(uint8(src[i])) << (8 * (31 - (i % 32)));
        }
    }

    /// The root of the tree over `words` placed from index zero.
    function _treeRoot(uint256[] memory words, uint256 depth) internal pure returns (bytes32) {
        if (words.length == 0) return Merkle.zero(depth);
        uint256 n = words.length;
        uint256[] memory level = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            level[i] = words[i];
        }
        bytes32 z;
        for (uint256 k = 0; k < depth; ++k) {
            uint256 m = (n + 1) / 2;
            for (uint256 p = 0; p < m; ++p) {
                uint256 r = 2 * p + 1 < n ? level[2 * p + 1] : uint256(z);
                level[p] = uint256(keccak256(abi.encode(level[2 * p], r)));
            }
            n = m;
            z = keccak256(abi.encode(z, z));
        }
        return bytes32(level[0]);
    }

    // ---------------------------------------------------------------- the step

    /// Executes one step from the state given by `pre` (`kind, call, pc, msize, memRoot`), its
    /// stack (bottom first), return data and context preimage, consuming the witness `w`: the
    /// memory proofs, the calldata proofs and, at a call boundary, the earlier outputs, each
    /// section preceded by its length in a word. Returns the hashes of the state before and
    /// after.
    function step(
        uint256[5] calldata pre,
        uint256[] calldata stack,
        bytes calldata ret,
        uint256[8] calldata cx,
        bytes calldata w
    ) external view returns (bytes32 before, bytes32 afterw) {
        if (pre[0] != RUNNING) {
            before = terminal(pre[0]);
            return (before, before);
        }
        Frame memory f = _frame(pre, stack, ret, cx);
        _sections(f, w);
        before = _hash(f);
        if (f.call >= CALLS) revert Witness();
        _exec(f);
        if (f.memAt != f.memEnd || f.cdAt != f.cdEnd) revert Witness();
        afterw = f.kind == RUNNING ? _hash(f) : terminal(f.kind);
    }

    function _frame(uint256[5] calldata pre, uint256[] calldata stack, bytes calldata ret, uint256[8] calldata cx)
        internal
        pure
        returns (Frame memory f)
    {
        f.kind = RUNNING;
        f.call = pre[1];
        f.pc = pre[2];
        f.msize = pre[3];
        f.memRoot = bytes32(pre[4]);
        f.stack = new uint256[](stack.length + 1);
        for (uint256 i = 0; i < stack.length; ++i) {
            f.stack[i] = stack[i];
        }
        f.sp = stack.length;
        f.ret = ret;
        f.cx = cx;
    }

    function _sections(Frame memory f, bytes calldata w) internal pure {
        uint256 at;
        uint256 end;
        assembly ("memory-safe") {
            at := w.offset
            end := add(w.offset, w.length)
        }
        f.memAt = at + 32;
        f.memEnd = f.memAt + _word(at);
        f.cdAt = f.memEnd + 32;
        f.cdEnd = f.cdAt + _word(f.memEnd);
        f.outsAt = f.cdEnd + 32;
        f.outsEnd = f.outsAt + _word(f.cdEnd);
        if (f.outsEnd != end) revert Witness();
    }

    function _hash(Frame memory f) internal pure returns (bytes32) {
        return running(f.call, f.pc, f.msize, f.memRoot, _ctx(f.cx), keccak256(f.ret), _stackHash(f));
    }

    function _stackHash(Frame memory f) internal pure returns (bytes32 h) {
        uint256[] memory s = f.stack;
        uint256 n = f.sp;
        assembly ("memory-safe") {
            h := keccak256(add(s, 0x20), shl(5, n))
        }
    }

    function _program(Frame memory f) internal view returns (Program memory) {
        return f.call == 0 ? lift : discharge;
    }

    function _reject(Frame memory f) internal pure {
        f.kind = REJECTED;
    }

    function _pop(Frame memory f) internal pure returns (uint256 v) {
        v = f.stack[--f.sp];
    }

    function _push(Frame memory f, uint256 v) internal pure {
        if (f.sp == f.stack.length) {
            uint256[] memory s = new uint256[](f.sp + 1);
            for (uint256 i = 0; i < f.sp; ++i) {
                s[i] = f.stack[i];
            }
            f.stack = s;
        }
        f.stack[f.sp++] = v;
    }

    /// Stack items an opcode consumes and produces, or `(type(uint256).max, 0)` for an opcode
    /// outside the implemented set.
    function _arity(uint256 op) internal pure returns (uint256 inputs, uint256 outputs) {
        if (op == 0x00 || op == 0x5b || op == 0xfe) return (0, 0);
        if (op >= 0x01 && op <= 0x07) return (2, 1);
        if (op == 0x08 || op == 0x09) return (3, 1);
        if (op == 0x0a || op == 0x0b) return (2, 1);
        if (op >= 0x10 && op <= 0x14) return (2, 1);
        if (op == 0x15 || op == 0x19 || op == 0x1e) return (1, 1);
        if (op >= 0x16 && op <= 0x18) return (2, 1);
        if (op >= 0x1a && op <= 0x1d) return (2, 1);
        if (op == 0x20) return (2, 1);
        if (op == 0x30 || (op >= 0x32 && op <= 0x34) || op == 0x36 || op == 0x38 || op == 0x3a || op == 0x3d || op == 0x46) {
            return (0, 1);
        }
        if (op == 0x35) return (1, 1);
        if (op == 0x37 || op == 0x39 || op == 0x3e || op == 0x5e) return (3, 0);
        if (op == 0x50) return (1, 0);
        if (op == 0x51) return (1, 1);
        if (op == 0x52 || op == 0x53) return (2, 0);
        if (op == 0x56) return (1, 0);
        if (op == 0x57) return (2, 0);
        if (op >= 0x58 && op <= 0x5a) return (0, 1);
        if (op >= 0x5f && op <= 0x7f) return (0, 1);
        if (op >= 0x80 && op <= 0x8f) return (op - 0x7f, op - 0x7f + 1);
        if (op >= 0x90 && op <= 0x9f) return (op - 0x8e, op - 0x8e);
        if (op >= 0xa0 && op <= 0xa4) return (op - 0x9e, 0);
        if (op == 0xf3 || op == 0xfd) return (2, 0);
        if (op == 0xfa) return (6, 1);
        return (type(uint256).max, 0);
    }

    function _exec(Frame memory f) internal view {
        Program memory prog = _program(f);
        uint256 op = _codeByte(prog, f.pc);
        (uint256 inputs, uint256 outputs) = _arity(op);
        if (inputs == type(uint256).max || f.sp < inputs || f.sp - inputs + outputs > MAX_STACK) {
            _reject(f);
            return;
        }
        if (op == 0xfe || op == 0xfd) {
            _reject(f);
            return;
        }
        if (op >= 0x5f && op <= 0x7f) {
            uint256 n = op - 0x5f;
            _push(f, n == 0 ? 0 : _codeWord(prog, f.pc + 1) >> (8 * (32 - n)));
            f.pc += 1 + n;
            return;
        }
        if (op >= 0x80 && op <= 0x8f) {
            _push(f, f.stack[f.sp - (op - 0x7f)]);
            f.pc += 1;
            return;
        }
        if (op >= 0x90 && op <= 0x9f) {
            uint256 d = f.sp - 1 - (op - 0x8f);
            (f.stack[f.sp - 1], f.stack[d]) = (f.stack[d], f.stack[f.sp - 1]);
            f.pc += 1;
            return;
        }
        if (op == 0x00) {
            _return(f, 0, 0);
            return;
        }
        if (op < 0x20) {
            _pure(f, op);
            f.pc += 1;
            return;
        }
        if (op == 0x56 || op == 0x57) {
            _jump(f, prog, op);
            return;
        }
        if (op == 0xf3) {
            uint256 o = _pop(f);
            uint256 len = _pop(f);
            _return(f, o, len);
            return;
        }
        _env(f, prog, op);
        if (f.kind == RUNNING) f.pc += 1;
    }

    function _pure(Frame memory f, uint256 op) internal pure {
        uint256 a = _pop(f);
        uint256 r;
        if (op == 0x15) {
            r = a == 0 ? 1 : 0;
        } else if (op == 0x19) {
            r = ~a;
        } else if (op == 0x1e) {
            r = _clz(a);
        } else if (op == 0x08 || op == 0x09) {
            uint256 b = _pop(f);
            uint256 n = _pop(f);
            assembly ("memory-safe") {
                switch op
                case 0x08 { r := addmod(a, b, n) }
                default { r := mulmod(a, b, n) }
            }
        } else {
            uint256 b = _pop(f);
            assembly ("memory-safe") {
                switch op
                case 0x01 { r := add(a, b) }
                case 0x02 { r := mul(a, b) }
                case 0x03 { r := sub(a, b) }
                case 0x04 { r := div(a, b) }
                case 0x05 { r := sdiv(a, b) }
                case 0x06 { r := mod(a, b) }
                case 0x07 { r := smod(a, b) }
                case 0x0a { r := exp(a, b) }
                case 0x0b { r := signextend(a, b) }
                case 0x10 { r := lt(a, b) }
                case 0x11 { r := gt(a, b) }
                case 0x12 { r := slt(a, b) }
                case 0x13 { r := sgt(a, b) }
                case 0x14 { r := eq(a, b) }
                case 0x16 { r := and(a, b) }
                case 0x17 { r := or(a, b) }
                case 0x18 { r := xor(a, b) }
                case 0x1a { r := byte(a, b) }
                case 0x1b { r := shl(a, b) }
                case 0x1c { r := shr(a, b) }
                case 0x1d { r := sar(a, b) }
            }
        }
        _push(f, r);
    }

    function _clz(uint256 a) internal pure returns (uint256 n) {
        if (a == 0) return 256;
        while (a >> 255 == 0) {
            a <<= 1;
            ++n;
        }
    }

    function _jump(Frame memory f, Program memory prog, uint256 op) internal view {
        uint256 dest = _pop(f);
        uint256 cond = op == 0x57 ? _pop(f) : 1;
        if (cond == 0) {
            f.pc += 1;
            return;
        }
        if (dest >= prog.codeLen || !CodeStore.isJump(prog.jumps, dest)) {
            _reject(f);
            return;
        }
        f.pc = dest;
    }

    function _env(Frame memory f, Program memory prog, uint256 op) internal view {
        if (op == 0x20) {
            uint256 o = _pop(f);
            uint256 len = _pop(f);
            if (!_expand(f, o, len)) return;
            bytes memory data = _readBytes(f, o, len);
            _commitExpand(f, o, len);
            _push(f, uint256(keccak256(data)));
        } else if (op == 0x30) {
            _push(f, uint160(prog.self));
        } else if (op == 0x32 || op == 0x33) {
            _push(f, uint160(caller));
        } else if (op == 0x34 || op == 0x3a) {
            _push(f, 0);
        } else if (op == 0x35) {
            _push(f, _calldataWord(f, _pop(f)));
        } else if (op == 0x36) {
            _push(f, f.cx[0]);
        } else if (op == 0x38) {
            _push(f, prog.codeLen);
        } else if (op == 0x3d) {
            _push(f, f.ret.length);
        } else if (op == 0x46) {
            _push(f, chainId);
        } else if (op == 0x37 || op == 0x39 || op == 0x3e) {
            _copy(f, prog, op);
        } else if (op == 0x50) {
            _pop(f);
        } else if (op == 0x51) {
            uint256 o = _pop(f);
            if (!_expand(f, o, 32)) return;
            bytes memory data = _readBytes(f, o, 32);
            _commitExpand(f, o, 32);
            _push(f, uint256(bytes32(data)));
        } else if (op == 0x52 || op == 0x53) {
            uint256 o = _pop(f);
            uint256 v = _pop(f);
            uint256 len = op == 0x52 ? 32 : 1;
            if (!_expand(f, o, len)) return;
            bytes memory data = op == 0x52 ? abi.encode(v) : abi.encodePacked(uint8(v));
            _writeBytes(f, o, data, len);
            _commitExpand(f, o, len);
        } else if (op == 0x58) {
            _push(f, f.pc);
        } else if (op == 0x59) {
            _push(f, f.msize);
        } else if (op == 0x5a) {
            _push(f, GAS_CONSTANT);
        } else if (op == 0x5b) {} else if (op == 0x5e) {
            uint256 dst = _pop(f);
            uint256 src = _pop(f);
            uint256 len = _pop(f);
            if (!_expand(f, src, len) || !_expand(f, dst, len)) return;
            bytes memory data = _readBytes(f, src, len);
            _writeBytes(f, dst, data, len);
            _commitExpand(f, src, len);
            _commitExpand(f, dst, len);
        } else if (op >= 0xa0 && op <= 0xa4) {
            uint256 o = _pop(f);
            uint256 len = _pop(f);
            for (uint256 i = 0; i < op - 0xa0; ++i) {
                _pop(f);
            }
            if (!_expand(f, o, len)) return;
            _commitExpand(f, o, len);
        } else if (op == 0xfa) {
            _staticcall(f);
        }
    }

    function _copy(Frame memory f, Program memory prog, uint256 op) internal view {
        uint256 dst = _pop(f);
        uint256 src = _pop(f);
        uint256 len = _pop(f);
        if (op == 0x3e && (len > f.ret.length || src > f.ret.length - len)) {
            _reject(f);
            return;
        }
        if (!_expand(f, dst, len)) return;
        if (len == 0) return;
        bytes memory data;
        if (op == 0x37) {
            if (src < f.cx[0]) {
                data = new bytes(f.cx[0] - src < len ? f.cx[0] - src : len);
                _calldataBytes(f, src, data);
            }
        } else if (op == 0x39) {
            if (src < prog.codeLen) {
                data = new bytes(prog.codeLen - src < len ? prog.codeLen - src : len);
                uint256 p;
                assembly ("memory-safe") {
                    p := add(data, 0x20)
                }
                CodeStore.read(prog.code, src, data.length, p);
            }
        } else {
            data = new bytes(len);
            for (uint256 i = 0; i < len; ++i) {
                data[i] = f.ret[src + i];
            }
        }
        _writeBytes(f, dst, data, len);
        _commitExpand(f, dst, len);
    }

    function _staticcall(Frame memory f) internal pure {
        uint256 g = _pop(f);
        uint256 to = _pop(f);
        uint256 ao = _pop(f);
        uint256 al = _pop(f);
        uint256 ro = _pop(f);
        uint256 rl = _pop(f);
        if (!_expand(f, ao, al) || !_expand(f, ro, rl)) return;
        if (to != 2) {
            _reject(f);
            return;
        }
        bytes memory args = _readBytes(f, ao, al);
        if (g < 60 + 12 * ((al + 31) / 32)) {
            f.ret = "";
            _push(f, 0);
        } else {
            bytes memory out = abi.encodePacked(sha256(args));
            f.ret = out;
            if (rl > 0) {
                uint256 n = rl < 32 ? rl : 32;
                bytes memory head = new bytes(n);
                for (uint256 i = 0; i < n; ++i) {
                    head[i] = out[i];
                }
                _writeBytes(f, ro, head, n);
            }
            _push(f, 1);
        }
        _commitExpand(f, ao, al);
        _commitExpand(f, ro, rl);
    }

    // ---------------------------------------------------------------- memory

    /// Whether `[o, o + len)` stays within the machine's memory; rejects if not.
    function _expand(Frame memory f, uint256 o, uint256 len) internal pure returns (bool) {
        if (len == 0) return true;
        if (o > (32 << MEM_DEPTH) || len > (32 << MEM_DEPTH) || o + len > (32 << MEM_DEPTH)) {
            _reject(f);
            return false;
        }
        return true;
    }

    function _commitExpand(Frame memory f, uint256 o, uint256 len) internal pure {
        if (len == 0) return;
        uint256 top = (o + len + 31) / 32 * 32;
        if (top > f.msize) f.msize = top;
    }

    /// The next memory proof, checked to cover words `[lo, lo + n)`.
    function _memProof(Frame memory f, uint256 lo, uint256 n)
        internal
        pure
        returns (uint256[] memory values, bytes32[] memory proof)
    {
        if (_word(f.memAt) != lo || _word(f.memAt + 32) != n) revert Witness();
        values = _words(f.memAt + 64, n);
        uint256 p = _word(f.memAt + 64 + 32 * n);
        proof = _hashes(f.memAt + 96 + 32 * n, p);
        f.memAt += 96 + 32 * (n + p);
        if (f.memAt > f.memEnd) revert Witness();
    }

    /// The `len` bytes of memory at `o`, reading proved words below the current size and zeros
    /// above it.
    function _readBytes(Frame memory f, uint256 o, uint256 len) internal pure returns (bytes memory data) {
        data = new bytes(len);
        if (len == 0) return data;
        uint256 lo = o / 32;
        uint256 hi = (o + len + 31) / 32;
        uint256 top = f.msize / 32;
        if (lo >= top) return data;
        uint256 end = hi < top ? hi : top;
        (uint256[] memory values, bytes32[] memory proof) = _memProof(f, lo, end - lo);
        uint256 skip = o - lo * 32;
        uint256 avail = 32 * values.length - skip;
        uint256 n = len < avail ? len : avail;
        assembly ("memory-safe") {
            mcopy(add(data, 0x20), add(add(values, 0x20), skip), n)
        }
        if (Merkle.root(values, lo, MEM_DEPTH, proof) != f.memRoot) revert Witness();
    }

    /// Writes `len` bytes to memory at `o`: `data`, then zeros.
    function _writeBytes(Frame memory f, uint256 o, bytes memory data, uint256 len) internal pure {
        if (len == 0) return;
        uint256 lo = o / 32;
        uint256 top = f.msize / 32;
        uint256 end = (o + len + 31) / 32;
        if (end > top && !_nonzeroFrom(data, top * 32 > o ? top * 32 - o : 0)) end = top;
        if (end <= lo) return;
        (uint256[] memory before, bytes32[] memory proof) = _memProof(f, lo, end - lo);
        for (uint256 i = 0; i < before.length; ++i) {
            if (lo + i >= top && before[i] != 0) revert Witness();
        }
        uint256[] memory afterw = _overwrite(before, o - lo * 32, data, len);
        (bytes32 r0, bytes32 r1) = Merkle.roots(before, afterw, lo, MEM_DEPTH, proof);
        if (r0 != f.memRoot) revert Witness();
        f.memRoot = r1;
    }

    /// `words` with `len` bytes from byte `skip` replaced by `data` then zeros, clipped to the
    /// words.
    function _overwrite(uint256[] memory words, uint256 skip, bytes memory data, uint256 len)
        internal
        pure
        returns (uint256[] memory out)
    {
        uint256 m = words.length;
        out = new uint256[](m);
        uint256 room = 32 * m - skip;
        uint256 dn = data.length < room ? data.length : room;
        uint256 zn = (len < room ? len : room) - dn;
        assembly ("memory-safe") {
            let a := add(out, 0x20)
            mcopy(a, add(words, 0x20), shl(5, m))
            mcopy(add(a, skip), add(data, 0x20), dn)
            calldatacopy(add(add(a, skip), dn), calldatasize(), zn)
        }
    }

    /// Whether `data` has a nonzero byte at or after `from`.
    function _nonzeroFrom(bytes memory data, uint256 from) internal pure returns (bool nz) {
        uint256 len = data.length;
        assembly ("memory-safe") {
            let p := add(add(data, 0x20), from)
            let e := add(add(data, 0x20), len)
            for {} lt(p, e) { p := add(p, 32) } {
                let w := mload(p)
                let left := sub(e, p)
                if lt(left, 32) { w := shr(shl(3, sub(32, left)), w) }
                if w {
                    nz := 1
                    break
                }
            }
        }
    }

    // ---------------------------------------------------------------- calldata

    /// Arg words of the calldata, `[lo, hi)`, from the prefix and body trees; words past the
    /// calldata are zero.
    function _argWords(Frame memory f, uint256 lo, uint256 hi) internal pure returns (uint256[] memory out) {
        out = new uint256[](hi - lo);
        uint256 argWords = (f.cx[0] - 4) / 32;
        uint256 end = hi < argWords ? hi : argWords;
        uint256 p = f.cx[3];
        if (lo < end && lo < p) {
            uint256 e = end < p ? end : p;
            uint256[] memory v = _cdProof(f, lo, e - lo, PREFIX_DEPTH, bytes32(f.cx[2]), 0);
            for (uint256 i = 0; i < v.length; ++i) {
                out[i] = v[i];
            }
        }
        uint256 b = lo > p ? lo : p;
        if (b < end) {
            uint256[] memory v = _cdProof(f, b, end - b, BODY_DEPTH, bytes32(f.cx[4]), p);
            for (uint256 i = 0; i < v.length; ++i) {
                out[b - lo + i] = v[i];
            }
        }
    }

    function _cdProof(Frame memory f, uint256 lo, uint256 n, uint256 depth, bytes32 root, uint256 base)
        internal
        pure
        returns (uint256[] memory values)
    {
        if (_word(f.cdAt) != lo || _word(f.cdAt + 32) != n) revert Witness();
        values = _words(f.cdAt + 64, n);
        uint256 p = _word(f.cdAt + 64 + 32 * n);
        bytes32[] memory proof = _hashes(f.cdAt + 96 + 32 * n, p);
        f.cdAt += 96 + 32 * (n + p);
        if (f.cdAt > f.cdEnd) revert Witness();
        if (Merkle.root(values, lo - base, depth, proof) != root) revert Witness();
    }

    /// The calldata bytes `[o, o + data.length)` into `data`, which must not reach past the
    /// calldata.
    function _calldataBytes(Frame memory f, uint256 o, bytes memory data) internal pure {
        uint256 n = data.length;
        if (n == 0) return;
        uint256 at = 0;
        bytes memory sel = abi.encodePacked(uint32(f.cx[1]));
        while (at < n && o + at < 4) {
            data[at] = sel[o + at];
            ++at;
        }
        if (at == n) return;
        uint256 first = o + at - 4;
        uint256 lo = first / 32;
        uint256 hi = (o + n - 4 + 31) / 32;
        uint256[] memory w = _argWords(f, lo, hi);
        uint256 skip = first - lo * 32;
        uint256 rest = n - at;
        assembly ("memory-safe") {
            mcopy(add(add(data, 0x20), at), add(add(w, 0x20), skip), rest)
        }
    }

    function _calldataWord(Frame memory f, uint256 o) internal pure returns (uint256) {
        if (o >= f.cx[0]) return 0;
        uint256 n = f.cx[0] - o < 32 ? f.cx[0] - o : 32;
        bytes memory data = new bytes(n);
        _calldataBytes(f, o, data);
        bytes memory word = new bytes(32);
        for (uint256 i = 0; i < n; ++i) {
            word[i] = data[i];
        }
        return uint256(bytes32(word));
    }

    // ---------------------------------------------------------------- calls

    /// Ends the current call with the output at `[o, o + len)` and moves to the next call.
    function _return(Frame memory f, uint256 o, uint256 len) internal view {
        if (!_expand(f, o, len)) return;
        bytes memory output = _readBytes(f, o, len);
        _commitExpand(f, o, len);
        if (f.call == CALLS - 1) {
            f.kind = len == 32 && uint256(bytes32(output)) == 1 ? ACCEPTED : REJECTED;
            return;
        }
        uint256[8] memory cx;
        if (f.call == 0) {
            if (!_isArray(output, 0x20, 0)) {
                _reject(f);
                return;
            }
            cx = _toKeccakPart(output);
            cx[5] = uint256(keccak256(output));
        } else if (f.call == 1) {
            bytes memory out0 = _outputArg(f, f.cx[5]);
            if (!_isArray(output, 0x20, 0)) {
                _reject(f);
                return;
            }
            cx = _toRows(out0);
            cx[5] = f.cx[5];
            cx[6] = uint256(keccak256(output));
        } else {
            bytes memory out0 = _outputArg(f, f.cx[5]);
            bytes memory out1 = _outputArg(f, f.cx[6]);
            if (!_isArray(output, 0x40, 1)) {
                _reject(f);
                return;
            }
            cx = _toFinish(out0, out1, output);
            cx[5] = f.cx[5];
            cx[6] = f.cx[6];
            cx[7] = uint256(keccak256(output));
        }
        if (f.outsAt != f.outsEnd) revert Witness();
        f.call += 1;
        f.pc = 0;
        f.msize = 0;
        f.memRoot = Merkle.zero(MEM_DEPTH);
        f.sp = 0;
        f.ret = "";
        f.cx = cx;
    }

    /// The next earlier output in `outs`, checked against its committed hash.
    function _outputArg(Frame memory f, uint256 hash) internal pure returns (bytes memory out) {
        uint256 len = _word(f.outsAt);
        out = new bytes(len);
        uint256 src = f.outsAt + 32;
        assembly ("memory-safe") {
            calldatacopy(add(out, 0x20), src, len)
        }
        f.outsAt += 32 + (len + 31) / 32 * 32;
        if (f.outsAt > f.outsEnd || uint256(keccak256(out)) != hash) revert Witness();
    }

    /// Whether `out` is an ABI encoding of a `uint256[]` whose offset word, at `offsetAt`
    /// words before the extra ones, is `offset`, with `extra` single words after the offset.
    function _isArray(bytes memory out, uint256 offset, uint256 extra) internal pure returns (bool) {
        uint256 head = 32 * (1 + extra);
        if (out.length < head + 32 || _mword(out, 0) != offset) return false;
        uint256 n = _mword(out, head);
        return n <= (out.length - head - 32) / 32 && out.length == head + 32 + 32 * n;
    }

    function _mword(bytes memory b, uint256 at) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := mload(add(add(b, 0x20), at))
        }
    }

    function _arrayWords(bytes memory enc, uint256 at) internal pure returns (uint256 n) {
        n = _mword(enc, at);
    }

    function _toKeccakPart(bytes memory out0) internal pure returns (uint256[8] memory cx) {
        uint256 words = out0.length / 32;
        uint256[] memory prefix = new uint256[](words);
        for (uint256 i = 0; i < words; ++i) {
            prefix[i] = _mword(out0, 32 * i);
        }
        cx[0] = 4 + out0.length;
        cx[1] = uint32(KECCAK_PART);
        cx[2] = uint256(_treeRoot(prefix, PREFIX_DEPTH));
        cx[3] = words;
        cx[4] = uint256(Merkle.zero(BODY_DEPTH));
    }

    function _toRows(bytes memory out0) internal view returns (uint256[8] memory cx) {
        uint256 n0 = _arrayWords(out0, 32);
        uint256 s = 2 * n0 / 112;
        uint256 p = 4 + 1 + n0 + 1 + s + 1;
        uint256[] memory prefix = new uint256[](p);
        prefix[0] = 0x80;
        prefix[1] = 0x80 + 32 * (1 + n0);
        prefix[2] = 0;
        prefix[3] = prefix[1] + 32 * (1 + s);
        for (uint256 i = 0; i <= n0; ++i) {
            prefix[4 + i] = _mword(out0, 32 + 32 * i);
        }
        prefix[5 + n0] = s;
        prefix[p - 1] = streamLen;
        cx[0] = 4 + 32 * p + 32 * ((streamLen + 31) / 32);
        cx[1] = uint32(ROWS);
        cx[2] = uint256(_treeRoot(prefix, PREFIX_DEPTH));
        cx[3] = p;
        cx[4] = uint256(streamRoot);
    }

    function _toFinish(bytes memory out0, bytes memory out1, bytes memory out2)
        internal
        pure
        returns (uint256[8] memory cx)
    {
        uint256 n0 = _arrayWords(out0, 32);
        uint256 n1 = _arrayWords(out1, 32);
        uint256 n2 = _arrayWords(out2, 64);
        uint256 p = 4 + (1 + n0) + (1 + n1) + (1 + n2);
        uint256[] memory prefix = new uint256[](p);
        prefix[0] = 0x80;
        prefix[1] = 0x80 + 32 * (1 + n0);
        prefix[2] = prefix[1] + 32 * (1 + n1);
        prefix[3] = _mword(out2, 32);
        uint256 at = 4;
        for (uint256 i = 0; i <= n0; ++i) {
            prefix[at++] = _mword(out0, 32 + 32 * i);
        }
        for (uint256 i = 0; i <= n1; ++i) {
            prefix[at++] = _mword(out1, 32 + 32 * i);
        }
        for (uint256 i = 0; i <= n2; ++i) {
            prefix[at++] = _mword(out2, 64 + 32 * i);
        }
        cx[0] = 4 + 32 * p;
        cx[1] = uint32(FINISH);
        cx[2] = uint256(_treeRoot(prefix, PREFIX_DEPTH));
        cx[3] = p;
        cx[4] = uint256(Merkle.zero(BODY_DEPTH));
    }

    // ---------------------------------------------------------------- code and calldata words

    function _codeByte(Program memory prog, uint256 pc) internal view returns (uint256 b) {
        if (pc >= prog.codeLen) return 0;
        return _codeWord(prog, pc) >> 248;
    }

    /// The 32 code bytes at `at`, zero past the end.
    function _codeWord(Program memory prog, uint256 at) internal view returns (uint256 w) {
        uint256 p;
        assembly ("memory-safe") {
            p := mload(0x40)
            mstore(p, 0)
        }
        if (at < prog.codeLen) {
            uint256 n = prog.codeLen - at < 32 ? prog.codeLen - at : 32;
            CodeStore.read(prog.code, at, n, p);
        }
        assembly ("memory-safe") {
            w := mload(p)
        }
    }

    function _word(uint256 at) internal pure returns (uint256 v) {
        assembly ("memory-safe") {
            v := calldataload(at)
        }
    }

    function _words(uint256 at, uint256 n) internal pure returns (uint256[] memory v) {
        v = new uint256[](n);
        assembly ("memory-safe") {
            calldatacopy(add(v, 0x20), at, shl(5, n))
        }
    }

    function _hashes(uint256 at, uint256 n) internal pure returns (bytes32[] memory v) {
        v = new bytes32[](n);
        assembly ("memory-safe") {
            calldatacopy(add(v, 0x20), at, shl(5, n))
        }
    }
}
