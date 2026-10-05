// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {IWrapStage, IWrapStart} from "./Carry.sol";

/// Verification of a wrapped lift across transactions that each fit a block: a session holds the
/// hash of its state, every call advances it by one stage, and the last records the statement's
/// digest as accepted. A session belongs to its caller.
contract WrapSessions {
    uint256 internal constant DONE = 8;

    /// The contract running the first stage.
    address public immutable first;
    /// The contract running each later stage.
    mapping(uint256 => address) public route;
    /// The hash of each open session's state.
    mapping(bytes32 => bytes32) public head;
    /// Whether the lift with each statement digest is verified.
    mapping(bytes32 => bool) public accepted;

    event Accepted(bytes32 indexed digest);

    error StaleState();
    error NoRoute();
    error Unread();

    constructor(address first_, address[] memory later) {
        first = first_;
        for (uint256 i = 0; i < later.length; ++i) {
            route[2 + i] = later[i];
        }
    }

    /// Opens the caller's session `salt` on a lift against the expected output `output`, with its
    /// word counts, under `binding`; `data` is the start of the lift's encoding.
    function start(bytes32 salt, bytes calldata output, uint256 counts, bytes calldata binding, bytes calldata data)
        external
        returns (bytes memory state)
    {
        state = IWrapStart(first).start(output, counts, binding, data);
        head[keccak256(abi.encodePacked(msg.sender, salt))] = keccak256(state);
    }

    /// Advances the caller's session `salt`, whose current state is `state`, by one stage reading
    /// `data` from the lift's encoding at the state's cursor. The last stage must leave the cursor
    /// at `end`, the length of the lift's encoding the caller has sent.
    function advance(bytes32 salt, bytes calldata state, bytes calldata data) external returns (bytes memory next) {
        bytes32 id = keccak256(abi.encodePacked(msg.sender, salt));
        if (keccak256(state) != head[id]) revert StaleState();
        address target = route[uint256(bytes32(state[32:64]))];
        if (target == address(0)) revert NoRoute();
        // `state` is the encoding of one dynamic value: an offset word, then the value.
        bytes memory payload = bytes.concat(
            IWrapStage.run.selector,
            bytes32(uint256(0x40)),
            bytes32(0x40 + state.length - 32),
            state[32:],
            bytes32(data.length),
            data,
            new bytes((32 - data.length % 32) % 32)
        );
        (bool ok, bytes memory out) = target.staticcall(payload);
        if (!ok) {
            assembly ("memory-safe") {
                revert(add(out, 0x20), mload(out))
            }
        }
        next = abi.decode(out, (bytes));
        uint256 stage;
        bytes32 digest;
        assembly ("memory-safe") {
            stage := mload(add(next, 0x40))
            digest := mload(add(next, 0x60))
        }
        if (stage == DONE) {
            accepted[digest] = true;
            delete head[id];
            emit Accepted(digest);
        } else {
            head[id] = keccak256(next);
        }
    }
}
