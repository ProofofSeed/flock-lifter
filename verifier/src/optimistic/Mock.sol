// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// A stand-in for the lift contract with its interface, for testing the dispute machinery on a
/// short trace: it rejects a proof whose first byte is `0xff` and otherwise returns claims
/// derived from its inputs.
contract MockLift {
    error Proof();

    /// Stand-in claims for `proof` against `output`, `counts` and `binding`.
    function verify(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata proof)
        external
        pure
        returns (uint256[] memory claims)
    {
        if (proof.length == 0 || proof[0] == 0xff) revert Proof();
        claims = new uint256[](224);
        bytes32 h = keccak256(abi.encode(output, counts, binding));
        for (uint256 i = 0; i < 224; ++i) {
            h = keccak256(abi.encodePacked(h, proof[i % proof.length]));
            claims[i] = uint256(h);
        }
        claims[0] ^= uint256(sha256(proof));
    }
}

/// A stand-in for the discharge contract with its interface: it folds its inputs and checks the
/// stream's hash chain against the pinned digest.
contract MockDischarge {
    /// The digest the stream must hash to.
    bytes32 public immutable digest;

    error Stream();

    constructor(bytes32 digest_) {
        digest = digest_;
    }

    /// Stand-in Keccak part.
    function keccakPart(uint256[] calldata claims) external pure returns (uint256[] memory out) {
        out = new uint256[](128);
        for (uint256 i = 0; i < 128; ++i) {
            out[i] = claims[i % claims.length] ^ i;
        }
    }

    /// Stand-in stream fold.
    function rows(uint256[] calldata claims, uint256[] calldata state, bytes32 chain, bytes calldata segment)
        external
        pure
        returns (uint256[] memory out, bytes32 chainOut)
    {
        bytes32 hashed;
        for (uint256 off = 0; off < segment.length; off += 32768) {
            uint256 end = off + 32768 < segment.length ? off + 32768 : segment.length;
            hashed = keccak256(abi.encodePacked(hashed, segment[off:end]));
        }
        chainOut = keccak256(abi.encodePacked(chain, hashed));
        out = new uint256[](state.length);
        for (uint256 i = 0; i < state.length; ++i) {
            out[i] = state[i] ^ claims[i] ^ uint256(uint8(segment[i]));
        }
    }

    /// Stand-in final check.
    function finish(uint256[] calldata claims, uint256[] calldata part, uint256[] calldata state, bytes32 chain)
        external
        view
        returns (bool)
    {
        if (chain != digest) revert Stream();
        return part[0] == claims[0] && state.length == 2 * claims.length / 112;
    }
}
