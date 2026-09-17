// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {IStage, Staged} from "./Staged.sol";

interface ILiftStart {
    function start(bytes calldata output, uint256 counts, bytes calldata binding, uint256 n, uint256 chunk)
        external
        view
        returns (bytes memory, uint256[] memory);
}

interface IMatrixStart {
    function start(bytes32 digest, uint256[] calldata claims) external view returns (bytes memory, uint256[] memory);
}

/// Direct verification of a lift across transactions that each fit a block: a session holds the
/// hash of its state, and every call advances it by one stage run over a range of items. A lift
/// session ends by recording its statement digest with the hash of its matrix claims, and a matrix
/// session may only start on claims so recorded; it ends by accepting the digest.
contract FlockSessions {
    /// The contract starting lift sessions, for the pinned statement.
    address public immutable lift;
    /// The contract starting matrix sessions, for the pinned entry commitment.
    address public immutable matrix;
    /// The contract running each stage.
    mapping(uint256 => address) public route;

    /// The hash of each open session's state.
    mapping(bytes32 => bytes32) public head;
    /// The hash of the packed matrix claims of each verified lift, by statement digest.
    mapping(bytes32 => bytes32) public liftClaims;
    /// Whether the lift with each statement digest is verified, matrix proof included.
    mapping(bytes32 => bool) public accepted;

    event Lifted(bytes32 indexed digest, bytes32 claims);
    event Accepted(bytes32 indexed digest);

    error StaleState();
    error UnverifiedClaims();
    error NoRoute();

    constructor(address lift_, address matrix_, uint256[] memory stages, address[] memory targets) {
        lift = lift_;
        matrix = matrix_;
        for (uint256 i = 0; i < stages.length; ++i) {
            route[stages[i]] = targets[i];
        }
    }

    /// Opens the caller's session `salt` on a lift of `n` responses in chunks of `chunk`.
    function startLift(bytes32 salt, bytes calldata output, uint256 counts, bytes calldata binding, uint256 n, uint256 chunk)
        external
        returns (bytes32 id, bytes memory state, uint256[] memory want)
    {
        (state, want) = ILiftStart(lift).start(output, counts, binding, n, chunk);
        id = keccak256(abi.encodePacked(msg.sender, salt));
        head[id] = keccak256(state);
    }

    /// Opens the caller's session `salt` on the matrix proof of the lift with statement digest
    /// `digest`, whose packed matrix claims must be the ones its lift session recorded.
    function startMatrix(bytes32 salt, bytes32 digest, uint256[] calldata claims)
        external
        returns (bytes32 id, bytes memory state, uint256[] memory want)
    {
        bytes32 recorded = liftClaims[digest];
        if (recorded == bytes32(0) || recorded != keccak256(abi.encodePacked(claims))) revert UnverifiedClaims();
        (state, want) = IMatrixStart(matrix).start(digest, claims);
        id = keccak256(abi.encodePacked(msg.sender, salt));
        head[id] = keccak256(state);
    }

    /// Advances the caller's session `salt`, whose current state is `state`, over its stage's
    /// items up to `upto`, reading `data`.
    function advance(bytes32 salt, bytes calldata state, uint256 upto, bytes calldata data)
        external
        returns (bytes memory next, uint256[] memory want)
    {
        bytes32 id = keccak256(abi.encodePacked(msg.sender, salt));
        if (keccak256(state) != head[id]) revert StaleState();
        address target = route[uint256(bytes32(state[:32]))];
        if (target == address(0)) revert NoRoute();
        (next, want) = IStage(target).run(state, upto, data);
        uint256 nextStage;
        bytes32 digest;
        bytes32 claims;
        assembly ("memory-safe") {
            nextStage := mload(add(next, 0x20))
            digest := mload(add(next, 0x40))
            claims := mload(add(next, 0x60))
        }
        if (nextStage == Staged.LIFT_DONE) {
            liftClaims[digest] = claims;
            delete head[id];
            emit Lifted(digest, claims);
        } else if (nextStage == Staged.MATRIX_DONE) {
            accepted[digest] = true;
            delete head[id];
            emit Accepted(digest);
        } else {
            head[id] = keccak256(next);
        }
    }
}
