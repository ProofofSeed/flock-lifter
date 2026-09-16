// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Calldata} from "./Calldata.sol";
import {Constants} from "./Constants.sol";
import {FiatShamir, OutputShape} from "./FiatShamir.sol";
import {Meter} from "./Meter.sol";
import {Opening} from "./Opening.sol";
import {Claim, MatrixClaim, Piop, ZerocheckOut} from "./Piop.sol";
import {Transcript} from "./Transcript.sol";

/// The verifier of a lifted hardened-child proof of seed for one pinned statement circuit: every
/// chunk proof up to its matrix discharge, the global Fiat-Shamir gate, and the relying party's
/// checks on the statement. It returns the matrix claims its discharge must close.
contract FlockLift {
    bytes internal constant LIFT_VERSION = "pofseed-flock-lift-v1";
    uint256 internal constant MAX_CHUNK = 128;

    /// The structural fingerprint of the statement circuit, which fixes its chain code and index.
    bytes32 public immutable fingerprint;
    /// The parent chain code.
    bytes32 public immutable chainCode;
    /// The child index.
    uint32 public immutable index;
    /// The fewest responses a lift may carry.
    uint256 public immutable minResponses;
    /// Whether chunks are opened under Ligerito's `Slim` profile rather than `Fast`.
    bool public immutable slim;

    error Shape();
    error AssertionWord();
    error TooFewResponses();

    constructor(bytes32 fingerprint_, bytes32 chainCode_, uint32 index_, uint256 minResponses_, bool slim_) {
        slim = slim_;
        fingerprint = fingerprint_;
        chainCode = chainCode_;
        index = index_;
        minResponses = minResponses_;
    }

    /// The inputs of one lift verification, read from calldata.
    struct Lift {
        uint256 outputAt;
        uint256 outputLen;
        uint256 bindingAt;
        uint256 bindingLen;
        uint256 chunk;
        uint256 n;
        uint256 nIo;
        uint256 wordsAt;
        uint256 unopenedAt;
        uint256 chunksAt;
        bytes32 digest;
    }

    /// Verifies a lift against the expected output `output`, which ZKBoo serialised from
    /// `counts & 0xffff` 8-bit, `(counts >> 16) & 0xffff` 32-bit and `counts >> 32` 64-bit words,
    /// under `binding`.
    function verify(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata proof)
        external
        returns (uint256[] memory)
    {
        Meter.mark(100);
        OutputShape memory s = FiatShamir.shape(output, counts & 0xffff, (counts >> 16) & 0xffff, counts >> 32);
        if (s.counts[0] == 0 || output[s.at[0] + s.counts[0] - 1] != 0x01) revert AssertionWord();
        Lift memory l;
        l.outputAt = _offset(output);
        l.outputLen = output.length;
        l.bindingAt = _offset(binding);
        l.bindingLen = binding.length;
        l.chunksAt = _offset(proof);
        return _pack(_lift(s, l, _offset(proof) + proof.length));
    }

    /// The matrix claims flattened, 112 words each: `alpha, beta, z, running`, the row point,
    /// the column point, then the collapsed witness.
    function _pack(MatrixClaim[] memory claims) private pure returns (uint256[] memory out) {
        out = new uint256[](112 * claims.length);
        for (uint256 i = 0; i < claims.length; ++i) {
            MatrixClaim memory c = claims[i];
            uint256 b = 112 * i;
            out[b] = c.alpha;
            out[b + 1] = c.beta;
            out[b + 2] = c.z;
            out[b + 3] = c.running;
            for (uint256 k = 0; k < 22; ++k) {
                out[b + 4 + k] = c.xInnerRest[k];
                out[b + 26 + k] = c.rInnerRest[k];
            }
            for (uint256 k = 0; k < 64; ++k) {
                out[b + 48 + k] = c.zPartial[k];
            }
        }
    }

    function _lift(OutputShape memory s, Lift memory l, uint256 end) private returns (MatrixClaim[] memory claims) {
        uint256 p = l.chunksAt;
        l.chunk = Calldata.u32(p);
        l.n = Calldata.u32(p + 4);
        if (l.n < minResponses) revert TooFewResponses();
        if (l.chunk == 0 || l.chunk > MAX_CHUNK) revert Shape();
        l.nIo = 5 + 2 * ((8 * s.payload + 127) / 128);
        l.wordsAt = p + 8;
        l.unopenedAt = l.wordsAt + 16 * l.nIo * l.n;
        l.chunksAt = l.unopenedAt + 32 * l.n;
        l.digest = _statementDigest(l);
        claims = new MatrixClaim[]((l.n + l.chunk - 1) / l.chunk);
        uint256 at = l.chunksAt;
        for (uint256 i = 0; i < claims.length; ++i) {
            uint256 len = Calldata.u32(at);
            uint256 live = l.n - i * l.chunk < l.chunk ? l.n - i * l.chunk : l.chunk;
            claims[i] = _chunk(l, i, live, at + 4, len);
            at += 4 + len;
        }
        if (at != end) revert Shape();
        FiatShamir.gate(s, FiatShamir.GateArgs(l.outputAt, l.bindingAt, l.bindingLen, l.n, l.nIo, l.wordsAt, l.unopenedAt));
        Meter.mark(101);
    }

    function _framed(bytes memory tag, bytes memory body) private pure returns (bytes memory) {
        return abi.encodePacked(tag, bytes8(uint64(FiatShamir.uint64le(body.length))), body);
    }

    function _statementDigest(Lift memory l) private view returns (bytes32) {
        bytes memory out = new bytes(l.outputLen);
        bytes memory bind = new bytes(l.bindingLen);
        uint256 oa = l.outputAt;
        uint256 ol = l.outputLen;
        uint256 ba = l.bindingAt;
        uint256 bl = l.bindingLen;
        assembly ("memory-safe") {
            calldatacopy(add(out, 0x20), oa, ol)
            calldatacopy(add(bind, 0x20), ba, bl)
        }
        bytes memory idx = abi.encodePacked(bytes4(uint32(FiatShamir.uint64le(index) >> 32)));
        bytes memory responses = abi.encodePacked(bytes8(uint64(FiatShamir.uint64le(l.n))));
        bytes memory chunk = abi.encodePacked(bytes4(uint32(FiatShamir.uint64le(l.chunk) >> 32)));
        bytes memory head = abi.encodePacked(
            _framed(LIFT_VERSION, abi.encodePacked(fingerprint)),
            _framed("chain-code", abi.encodePacked(chainCode)),
            _framed("index", idx)
        );
        bytes memory tail = abi.encodePacked(_framed("binding", bind), _framed("responses", responses), _framed("chunk", chunk));
        return keccak256(bytes.concat(head, _framed("expected-output", out), tail));
    }

    /// Verifies chunk `i`, over `live` blocks, whose proof is the `len` calldata bytes at `at`.
    function _chunk(Lift memory l, uint256 i, uint256 live, uint256 at, uint256 len)
        private
        returns (MatrixClaim memory mc)
    {
        bytes memory domain = abi.encodePacked(LIFT_VERSION, l.digest, bytes8(uint64(FiatShamir.uint64le(i))));
        uint256 tr = Transcript.createFromMemory(domain);
        uint256 nu = 3;
        while ((1 << nu) < live) {
            ++nu;
        }
        Ctx memory x;
        x.tr = tr;
        x.phi = Constants.PHI8;
        x.wordsAt = l.wordsAt + 16 * l.nIo * i * l.chunk;
        x.live = live;
        x.nIo = l.nIo;
        x.nu = nu;
        x.m = Piop.K_LOG + nu;
        x.capAt = at;
        x.end = at + len;
        return _verifyChunk(x);
    }

    /// The fixed inputs of one chunk verification.
    struct Ctx {
        uint256 tr;
        bytes phi;
        uint256 wordsAt;
        uint256 live;
        uint256 nIo;
        uint256 nu;
        uint256 m;
        uint256 capAt;
        uint256 capLen;
        uint256 end;
    }

    function _verifyChunk(Ctx memory x) private returns (MatrixClaim memory mc) {
        Piop.observeWords(x.tr, x.wordsAt, x.live, x.nIo, x.nu);
        Meter.mark(1);
        x.capLen = 1 << Constants.ligerito(x.m, slim).depths[0][0];
        uint256 p = x.capAt + 32 * x.capLen;
        Transcript.label(x.tr, Constants.L_R1CS_0, Constants.L_R1CS_1, Constants.L_R1CS_LEN);
        Transcript.header(x.tr, 5, 0, 32);
        Transcript.raw(x.tr, _statementDigestOf(x.m));
        Transcript.header(x.tr, 5, 0, 32 * x.capLen);
        Transcript.bytesFromCalldata(x.tr, x.capAt, 32 * x.capLen);
        ZerocheckOut memory zc;
        (p, zc) = Piop.zerocheck(x.tr, x.phi, p, x.m);
        Meter.mark(2);
        Claim[] memory cl = new Claim[](3);
        (p, mc, cl[0]) = Piop.lincheck(x.tr, x.phi, p, zc);
        Meter.mark(3);
        cl[1] = Claim(zc.z, zc.rRest, zc.c);
        cl[2] = Piop.ioClaim(x.tr, x.phi, x.wordsAt, x.live, x.nIo, x.nu);
        Meter.mark(4);
        Opening.verify(x.tr, x.phi, p, x.end, Constants.ligerito(x.m, slim), x.m, x.capAt, x.capLen, cl);
        Meter.mark(5);
    }

    function _statementDigestOf(uint256 m) private pure returns (bytes32) {
        if (m == 31) return Constants.STATEMENT_DIGEST_31;
        if (m == 32) return Constants.STATEMENT_DIGEST_32;
        if (m == 33) return Constants.STATEMENT_DIGEST_33;
        if (m == 34) return Constants.STATEMENT_DIGEST_34;
        if (m == 35) return Constants.STATEMENT_DIGEST_35;
        revert Shape();
    }

    function _offset(bytes calldata b) private pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }
}
