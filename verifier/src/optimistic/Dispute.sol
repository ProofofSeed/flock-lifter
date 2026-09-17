// SPDX-License-Identifier: LGPL-3.0-or-later
pragma solidity ^0.8.30;

import {OneStep} from "./OneStep.sol";

/// Optimistic acceptance of lifted proofs: an asserter uploads a lift and its matrix proof,
/// asserts that the machine's run of their direct verification ends accepted after a given
/// number of steps, and posts a bond; anyone may challenge within a window, and each challenge
/// is settled by a dissection of the asserter's trace down to one step, which the machine
/// re-executes.
contract Dispute {
    /// Argument words per upload chunk: a subtree of this depth.
    uint256 internal constant CHUNK_DEPTH = 13;
    uint256 internal constant BODY_DEPTH = 24;

    enum Turn {
        Asserter,
        Challenger,
        Done
    }

    struct Upload {
        address owner;
        uint256 len;
        uint256 received;
        bytes32[] subroots;
        bytes32 root;
        uint256 head;
    }

    struct Assertion {
        address asserter;
        bytes32 statement;
        bytes32 start;
        uint256 steps;
        uint256 deadline;
        uint256 open;
        bool refuted;
        bool confirmed;
        bool paid;
    }

    struct Game {
        uint256 assertion;
        address challenger;
        uint256 lo;
        uint256 hi;
        bytes32 loHash;
        bytes32 hiHash;
        bytes32 mids;
        Turn turn;
        uint256 deadline;
        bool challengerWon;
    }

    /// The machine.
    OneStep public immutable machine;
    /// The asserter's and each challenger's bond.
    uint256 public immutable bond;
    /// Seconds an assertion stays open to challenges.
    uint256 public immutable window;
    /// Seconds each side has for each move.
    uint256 public immutable moveTime;
    /// Points per dissection, as sub-intervals.
    uint256 public immutable arity;

    Upload[] internal uploads;
    Assertion[] public assertions;
    Game[] public games;
    /// Whether a statement has an accepted lift.
    mapping(bytes32 => bool) public accepted;

    error Bond();
    error NotYours();
    error Late();
    error Early();
    error BadMove();
    error Settled();

    event Asserted(uint256 indexed id, bytes32 statement, bytes32 start, uint256 steps);
    event Challenged(uint256 indexed game, uint256 indexed assertion);
    event Dissected(uint256 indexed game, bytes32[] mids);
    event Chosen(uint256 indexed game, uint256 lo, uint256 hi);
    event Resolved(uint256 indexed game, bool challengerWon);

    constructor(OneStep machine_, uint256 bond_, uint256 window_, uint256 moveTime_, uint256 arity_) {
        require(arity_ >= 2, "arity");
        machine = machine_;
        bond = bond_;
        window = window_;
        moveTime = moveTime_;
        arity = arity_;
    }

    // ---------------------------------------------------------------- data

    /// Starts an upload of `len` proof bytes.
    function beginUpload(uint256 len) external returns (uint256 id) {
        id = uploads.length;
        uploads.push();
        uploads[id].owner = msg.sender;
        uploads[id].len = len;
    }

    /// Uploads the next chunk: `2^CHUNK_DEPTH` words of proof bytes, or the rest.
    function upload(uint256 id, bytes calldata chunk) external {
        Upload storage u = uploads[id];
        if (u.owner != msg.sender) revert NotYours();
        uint256 full = 32 << CHUNK_DEPTH;
        uint256 left = u.len - u.received;
        if (chunk.length != (left < full ? left : full) || u.root != 0) revert BadMove();
        if (u.received == 0) u.head = _head(chunk);
        u.received += chunk.length;
        u.subroots.push(_chunkRoot(chunk));
    }

    /// Completes an upload, returning the root of its word tree.
    function finishUpload(uint256 id) external returns (bytes32 root) {
        Upload storage u = uploads[id];
        if (u.received != u.len || u.root != 0) revert BadMove();
        uint256 n = u.subroots.length;
        bytes32[] memory level = new bytes32[](n == 0 ? 1 : n);
        for (uint256 i = 0; i < n; ++i) {
            level[i] = u.subroots[i];
        }
        bytes32 z = _zero(CHUNK_DEPTH);
        if (n == 0) level[0] = z;
        n = level.length;
        for (uint256 k = CHUNK_DEPTH; k < BODY_DEPTH; ++k) {
            uint256 m = (n + 1) / 2;
            for (uint256 p = 0; p < m; ++p) {
                bytes32 r = 2 * p + 1 < n ? level[2 * p + 1] : z;
                level[p] = keccak256(abi.encode(level[2 * p], r));
            }
            n = m;
            z = keccak256(abi.encode(z, z));
        }
        root = level[0];
        u.root = root;
    }

    /// The root and length of a completed upload.
    function uploaded(uint256 id) external view returns (bytes32, uint256) {
        return (uploads[id].root, uploads[id].len);
    }

    /// The first word of `chunk`, zero-padded.
    function _head(bytes calldata chunk) internal pure returns (uint256 h) {
        uint256 n = chunk.length < 32 ? chunk.length : 32;
        assembly ("memory-safe") {
            mstore(0, 0)
            calldatacopy(0, chunk.offset, n)
            h := mload(0)
        }
    }

    function _zero(uint256 depth) internal pure returns (bytes32 z) {
        for (uint256 k = 0; k < depth; ++k) {
            z = keccak256(abi.encode(z, z));
        }
    }

    /// The root of the depth-`CHUNK_DEPTH` tree over the words of `chunk`, zero-padded.
    function _chunkRoot(bytes calldata chunk) internal pure returns (bytes32 root) {
        uint256 words = 1 << CHUNK_DEPTH;
        uint256 len = chunk.length;
        assembly ("memory-safe") {
            let buf := mload(0x40)
            let size := shl(5, words)
            calldatacopy(buf, chunk.offset, len)
            calldatacopy(add(buf, len), calldatasize(), sub(size, len))
            let n := words
            for {} gt(n, 1) {} {
                let m := shr(1, n)
                for { let p := 0 } lt(p, m) { p := add(p, 1) } {
                    mstore(add(buf, shl(5, p)), keccak256(add(buf, shl(6, p)), 0x40))
                }
                n := m
            }
            root := mload(buf)
        }
    }

    // ---------------------------------------------------------------- assertions

    /// The key under which a statement's acceptance is recorded.
    function statementKey(bytes calldata output, uint256 counts, bytes calldata binding) public pure returns (bytes32) {
        return keccak256(abi.encode(output, counts, binding));
    }

    /// Asserts that the verification of the lift in upload `liftData` with the matrix proof in
    /// upload `matrixData` against the statement ends accepted after `steps` steps.
    function assertLift(
        bytes calldata output,
        uint256 counts,
        bytes calldata binding,
        uint256 liftData,
        uint256 matrixData,
        uint256 steps
    ) external payable returns (uint256 id) {
        if (msg.value != bond) revert Bond();
        Upload storage l = uploads[liftData];
        Upload storage m = uploads[matrixData];
        if (l.owner != msg.sender || l.root == 0 || m.owner != msg.sender || m.root == 0 || steps == 0) {
            revert BadMove();
        }
        bytes32 start = machine.initial(output, counts, binding, [uint256(l.root), l.len, l.head, uint256(m.root), m.len]);
        id = assertions.length;
        assertions.push(
            Assertion({
                asserter: msg.sender,
                statement: statementKey(output, counts, binding),
                start: start,
                steps: steps,
                deadline: block.timestamp + window,
                open: 0,
                refuted: false,
                confirmed: false,
                paid: false
            })
        );
        emit Asserted(id, assertions[id].statement, start, steps);
    }

    /// Challenges assertion `id`.
    function challenge(uint256 id) external payable returns (uint256 g) {
        if (msg.value != bond) revert Bond();
        Assertion storage a = assertions[id];
        if (block.timestamp >= a.deadline || a.refuted) revert Late();
        a.open += 1;
        g = games.length;
        games.push(
            Game({
                assertion: id,
                challenger: msg.sender,
                lo: 0,
                hi: a.steps,
                loHash: a.start,
                hiHash: machine.terminal(1),
                mids: 0,
                turn: Turn.Asserter,
                deadline: block.timestamp + moveTime,
                challengerWon: false
            })
        );
        emit Challenged(g, id);
    }

    /// The step indices that dissect `[lo, hi)`, ends included.
    function points(uint256 lo, uint256 hi) public view returns (uint256[] memory p) {
        uint256 span = hi - lo;
        uint256 k = span < arity ? span : arity;
        p = new uint256[](k + 1);
        for (uint256 j = 0; j <= k; ++j) {
            p[j] = lo + (span * j) / k;
        }
    }

    /// The asserter's move: the state hashes at the interior points of the current interval.
    function dissect(uint256 g, bytes32[] calldata mids) external {
        Game storage x = games[g];
        Assertion storage a = assertions[x.assertion];
        if (msg.sender != a.asserter) revert NotYours();
        if (x.turn != Turn.Asserter || x.hi - x.lo < 2) revert BadMove();
        if (block.timestamp >= x.deadline) revert Late();
        uint256 span = x.hi - x.lo;
        if (mids.length != (span < arity ? span : arity) - 1) revert BadMove();
        x.mids = keccak256(abi.encodePacked(mids));
        x.turn = Turn.Challenger;
        x.deadline = block.timestamp + moveTime;
        emit Dissected(g, mids);
    }

    /// The challenger's move: the sub-interval `j` it disputes, given the asserter's hashes.
    function choose(uint256 g, bytes32[] calldata mids, uint256 j) external {
        Game storage x = games[g];
        if (msg.sender != x.challenger) revert NotYours();
        if (x.turn != Turn.Challenger || keccak256(abi.encodePacked(mids)) != x.mids) revert BadMove();
        if (block.timestamp >= x.deadline) revert Late();
        if (j > mids.length) revert BadMove();
        uint256[] memory p = points(x.lo, x.hi);
        bytes32 left = j == 0 ? x.loHash : mids[j - 1];
        bytes32 right = j == mids.length ? x.hiHash : mids[j];
        x.lo = p[j];
        x.hi = p[j + 1];
        x.loHash = left;
        x.hiHash = right;
        x.mids = 0;
        x.turn = Turn.Asserter;
        x.deadline = block.timestamp + moveTime;
        emit Chosen(g, x.lo, x.hi);
    }

    /// Settles a game narrowed to one step by re-executing it: the challenger wins unless the
    /// step leads from the agreed state to the asserter's.
    function resolve(
        uint256 g,
        uint256[5] calldata pre,
        uint256[] calldata stack,
        bytes calldata ret,
        uint256[8] calldata cx,
        bytes calldata w
    ) external {
        Game storage x = games[g];
        if (x.turn == Turn.Done || x.hi - x.lo != 1) revert BadMove();
        (bytes32 before, bytes32 afterw) = machine.step(pre, stack, ret, cx, w);
        if (before != x.loHash) revert BadMove();
        _settle(g, afterw != x.hiHash);
    }

    /// Settles a game whose side to move let its time run out.
    function timeout(uint256 g) external {
        Game storage x = games[g];
        if (x.turn == Turn.Done) revert Settled();
        if (block.timestamp < x.deadline) revert Early();
        _settle(g, x.turn == Turn.Asserter);
    }

    function _settle(uint256 g, bool challengerWon) internal {
        Game storage x = games[g];
        Assertion storage a = assertions[x.assertion];
        x.turn = Turn.Done;
        x.challengerWon = challengerWon;
        a.open -= 1;
        emit Resolved(g, challengerWon);
        if (challengerWon) {
            uint256 prize = bond;
            if (!a.refuted) {
                a.refuted = true;
                prize += bond;
            }
            payable(x.challenger).transfer(prize);
        } else {
            payable(a.asserter).transfer(bond);
        }
    }

    /// Confirms an assertion that outlived its window and every challenge, returning the
    /// asserter's bond.
    function confirm(uint256 id) external {
        Assertion storage a = assertions[id];
        if (block.timestamp < a.deadline) revert Early();
        if (a.open != 0 || a.refuted || a.confirmed) revert BadMove();
        a.confirmed = true;
        accepted[a.statement] = true;
        payable(a.asserter).transfer(bond);
    }

    /// The number of games.
    function gameCount() external view returns (uint256) {
        return games.length;
    }
}
