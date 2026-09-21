// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {Constants} from "./Constants.sol";
import {Meter} from "./Meter.sol";
import {Opening} from "./Opening.sol";
import {Claim, MatrixClaim, Piop, ZerocheckOut} from "./Piop.sol";
import {Transcript} from "./Transcript.sol";

/// The verifier of one Flock chunk proof of the lift, up to the lincheck's matrix discharge,
/// whose equation it returns.
///
/// Its runtime code exceeds EIP-170's limit, so it cannot be deployed on mainnet (see
/// `verifier/README.md`).
contract FlockVerifier {
    error Shape();

    function statementDigest(uint256 m) internal pure returns (bytes32) {
        if (m == 31) return Constants.STATEMENT_DIGEST_31;
        if (m == 32) return Constants.STATEMENT_DIGEST_32;
        if (m == 33) return Constants.STATEMENT_DIGEST_33;
        if (m == 34) return Constants.STATEMENT_DIGEST_34;
        if (m == 35) return Constants.STATEMENT_DIGEST_35;
        revert Shape();
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

    /// Verifies the chunk proof `proof` over `live` blocks whose published words are `words`
    /// (sixteen bytes each, in Flock's native layout), under the transcript domain `domain`.
    function verifyChunk(bytes calldata domain, bytes calldata words, uint256 live, bytes calldata proof)
        external
        returns (MatrixClaim memory)
    {
        Meter.mark(0);
        if (live == 0 || words.length % (16 * live) != 0) revert Shape();
        Ctx memory x;
        x.wordsAt = _offset(words);
        x.live = live;
        x.nIo = words.length / (16 * live);
        x.nu = 3;
        while ((1 << x.nu) < live) {
            ++x.nu;
        }
        x.m = Piop.K_LOG + x.nu;
        x.phi = Constants.PHI8;
        x.tr = Transcript.create(_offset(domain), domain.length);
        x.capAt = _offset(proof);
        x.end = x.capAt + proof.length;
        return _verify(x);
    }

    function _verify(Ctx memory x) private returns (MatrixClaim memory mc) {
        Piop.observeWords(x.tr, x.wordsAt, x.live, x.nIo, x.nu);
        Meter.mark(1);
        x.capLen = 1 << Constants.ligerito(x.m, false).depths[0][0];
        uint256 p = x.capAt + 32 * x.capLen;
        Transcript.label(x.tr, Constants.L_R1CS_0, Constants.L_R1CS_1, Constants.L_R1CS_LEN);
        Transcript.header(x.tr, 5, 0, 32);
        _observeDigest(x.tr, statementDigest(x.m));
        Transcript.header(x.tr, 5, 0, 32 * x.capLen);
        Transcript.bytesFromCalldata(x.tr, x.capAt, 32 * x.capLen);
        ZerocheckOut memory zc;
        (p, zc) = Piop.zerocheck(x.tr, x.phi, p, x.m);
        Meter.mark(2);
        Claim[] memory claims = new Claim[](3);
        (p, mc, claims[0]) = Piop.lincheck(x.tr, x.phi, p, zc);
        Meter.mark(3);
        claims[1] = Claim(zc.z, zc.rRest, zc.c);
        claims[2] = Piop.ioClaim(x.tr, x.phi, x.wordsAt, x.live, x.nIo, x.nu);
        Meter.mark(4);
        Opening.verify(x.tr, x.phi, p, x.end, Constants.ligerito(x.m, false), x.m, x.capAt, x.capLen, claims);
        Meter.mark(5);
    }

    function _offset(bytes calldata b) private pure returns (uint256 o) {
        assembly ("memory-safe") {
            o := b.offset
        }
    }

    function _observeDigest(uint256 tr, bytes32 digest) private pure {
        assembly ("memory-safe") {
            let l := mload(add(tr, 0x20))
            mstore(add(add(tr, 0x40), l), digest)
            mstore(add(tr, 0x20), add(l, 32))
        }
    }
}
