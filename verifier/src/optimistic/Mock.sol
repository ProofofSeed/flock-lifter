// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

/// A stand-in for the lift contract with its interface and pinned statement, for testing the
/// dispute machinery on a short trace: it rejects a proof whose first byte is `0xff` and
/// otherwise returns claims derived from its inputs.
contract MockLift {
    /// The circuit fingerprint.
    bytes32 public immutable fingerprint;
    /// The chain code.
    bytes32 public immutable chainCode;
    /// The child index.
    uint32 public immutable index;

    error Proof();

    constructor(bytes32 fingerprint_, bytes32 chainCode_, uint32 index_) {
        fingerprint = fingerprint_;
        chainCode = chainCode_;
        index = index_;
    }

    /// Stand-in claims for `proof` against `output`, `counts` and `binding`.
    function verify(bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata proof)
        external
        view
        returns (uint256[] memory claims)
    {
        if (proof.length == 0 || proof[0] == 0xff) revert Proof();
        claims = new uint256[](224);
        bytes32 h = keccak256(abi.encode(output, counts, binding, fingerprint));
        for (uint256 i = 0; i < 224; ++i) {
            h = keccak256(abi.encodePacked(h, proof[i % proof.length]));
            claims[i] = uint256(h);
        }
        claims[0] ^= uint256(sha256(proof));
    }
}

/// A stand-in for the matrix contract with its interface: it accepts a proof whose first byte is
/// its first claim's first byte, under a nonzero digest.
contract MockMatrix {
    /// A stand-in entry commitment.
    bytes32 public constant capHash = keccak256("stand-in entry commitment");
    /// A stand-in profile.
    bool public constant slim = false;
    /// A stand-in first Keccak sub-block.
    uint256 public constant firstKeccak = 7;
    /// A stand-in Keccak sub-block count.
    uint256 public constant keccakSubs = 11;

    error Proof();

    /// Stand-in verification of `proof` for `claims` under `digest`.
    function verify(uint256[] calldata claims, bytes32 digest, bytes calldata proof) external pure returns (bool) {
        if (digest == 0 || claims.length != 224 || proof.length < 64) revert Proof();
        bytes32 h = sha256(proof);
        uint256 acc = uint256(h) ^ uint256(digest);
        for (uint256 i = 0; i < claims.length; ++i) {
            acc = uint256(keccak256(abi.encode(acc, claims[i])));
        }
        if (uint8(proof[0]) != claims[0] >> 248) revert Proof();
        return acc != 0;
    }
}
