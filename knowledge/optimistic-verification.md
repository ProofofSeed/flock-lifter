# Optimistic verification of a Flock lift

Status: prototype, 2026-09-17, re-measured the same day on the current contracts, and again on zkboo 1.3.0 on 2026-09-21. It is an addition to direct verification, which it leaves unchanged.

A lift can be accepted on Ethereum in two ways, and both are built:

- **Direct verification** (`evm-verifier.md`, `committed-matrix.md`). Anyone calls `FlockLift.verify` on the lift, which returns the chunks' matrix claims. Then `FlockMatrix.verify` is called on those claims, the lift's statement digest and the matrix proof. At 219 responses the two calls cost 759.0 M gas with the cap lifted. The staged route runs the same checks in 106 transactions under the cap, for 889.0 M gas (`staged-verification.md`).
- **Optimistic verification** (this record). An asserter uploads the lift and its matrix proof, asserts that those same two calls accept, and posts a bond. Anyone may challenge within a window. A disagreement is narrowed to one EVM step of the two calls, and `OneStep` re-executes that step. Every transaction fits the 2^24 gas cap.

The two routes check the same thing: the optimistic machine runs the direct route's deployed bytecode, unmodified. What differs is who pays for the checking, and when.

## What is asserted

The machine is the EVM running the statement's `FlockLift` and `FlockMatrix` runtime bytecode as two chained calls:

1. `FlockLift.verify(output, counts, binding, lift)`;
2. `FlockMatrix.verify(claims, digest, matrixProof)`, where `claims` is the first call's output.

Here `digest` is the statement digest that `FlockLift` computes internally. The single-call harness passes it as an argument, and the staged route takes it from the lift session's record. The machine computes it on chain, in `OneStep.statementDigest`, from:
- the statement the lift contract pins;
- the output and binding;
- the chunk size and response count, taken from the first word of the uploaded lift.

The Rust port of that digest is checked against the lifter's own `Statement::digest`.

The machine departs from the EVM in four ways. Each can only turn an accepting run into a rejecting one:
- `GAS` pushes 2^32;
- the only callable address is the SHA-256 precompile;
- memory is capped at 2^22 words (134 MB);
- any opcode outside the implemented set rejects, as do reverts and every exceptional halt.

On the valid 219-response lift the trace has no unsupported opcode and no call outside SHA-256, and peak memory is 1.9 MB.

**What a state commits to.**
- the call and the program counter;
- the stack;
- memory, as a Keccak Merkle tree of depth 22 over its words, with its size;
- the return data;
- the call's context.

**What the context commits to.**
- the calldata, as a selector, a prefix tree of depth 10 and a body tree of depth 24;
- three words carrying what the next call needs. For the lift call these are the statement digest and the matrix proof's root and length. For the matrix call, the hash of the lift call's output.

**The bodies.** The lift call's body is the uploaded lift, and the matrix call's body is the uploaded matrix proof. At the lift call's return, the step itself builds the matrix call's calldata commitment from the returned claims.

Accepting and rejecting states are terminal and absorb further steps, so a trace of any claimed length is well defined.

## What is fixed per statement

`OneStep` holds the runtime bytecode of the statement's two contracts in data-holding contracts, 24 KB each. Both exceed EIP-170's limit for an executable contract (about 53 KB each), but neither has to run, and neither is deployed: their runtime code is produced off chain by running their initcode. At construction `OneStep` reads what they pin from that held code, at the offsets of their immutables (from the compiler's immutable references, passed to the constructor):
- from `FlockLift`: the circuit fingerprint, chain code and index;
- from `FlockMatrix`: the entry-commitment cap hash, the profile, the first Keccak sub-block and the sub-block count.

It exposes all of them, with `codeHash(which)` for the held bytecode. Checking a deployment therefore means checking the two code hashes and that the seven offsets are those of the immutables; the harness asserts that the values `OneStep` read are the ones the programs were built with. The harness installs the two programs in its EVM for the off-chain run and enforces the code-size limit on every contract it deploys.

## The protocol

1. **Deployment, once per statement.** The held bytecode, `OneStep` and its two jump-destination bitmaps (computed on chain), then `Dispute`, with a bond, a challenge window, a time per move and a dissection arity.
2. **Upload.** The asserter sends the lift (1,215,008 bytes) and the matrix proof (437,664 bytes) as two uploads, in 262,144-byte chunks. The contract hashes each chunk into a subtree root, combines the subtrees into the root of a depth-24 word tree, and keeps the lift's first word. The bytes stay available as transaction calldata.
3. **Assertion.** `assertLift(output, counts, binding, liftUpload, matrixUpload, steps)` takes the bond. It computes the machine's initial state on chain, including the statement digest, and records the claim that state `steps` is the accepting terminal.
4. **Challenge.** Anyone may challenge within the window, with the same bond. Each challenge is a separate game over `[0, steps]`.
5. **Dissection.** The asserter posts the state hashes at the `k − 1` interior points of the current interval, and the challenger names a sub-interval. This repeats until one step is left, each move within one move time.
6. **Resolution.** Anyone calls `resolve` with the agreed state's preimage and the step's witness, which is memory and calldata range proofs. `OneStep` re-executes the step, and the challenger wins unless the result is the asserter's state. If nobody resolves in time, the challenger wins, and whoever lets a move time run out loses.
7. **Settlement.**
   - A winning challenger takes its bond back, plus the asserter's bond if it is the first to win.
   - A winning asserter takes the challenger's bond.
   - After the window, an assertion with no open or lost game is confirmed, its bond is returned, and its statement reads as accepted.

## Firm numbers

### On zkboo 1.3.0

Re-measured on 2026-09-21 on the hardened-child circuit of zkboo 1.3.0 (`zkboo-1.3.0-migration.md`), with `OneStep` reading its pins from the held code (`fixtures/optimistic-*-2026-09-21-zkboo-1.3.0.summary.log`):
- **Trace.** 237,087,171 steps: 134,107,441 in the lift call and 102,979,730 in the matrix call. The tampered lift is rejected after 26,664,000 steps, the tampered matrix proof after 203,556,551.
- **Heaviest step.** The same fold of the counts, at step 59,116,487 of the matrix call: 6,787,958 gas alone, **6,960,055 resolved inside a game, with 9.82 M to spare**.
- **Games.** All 16 games were won by the truthful side, at 7 dissections each where the game went the distance.
- **One-step check.** `OneStep` agreed with revm on 50,432 steps, with no mismatch.
- **Costs.** Deployment is 44,730,170 gas in 11 transactions: the one-step contract costs 1,378 gas more now that it reads its pins from the held code, and each jump table about 2,000 more. The unchallenged path is 63,677,857 gas in 13 transactions. The worst dispute is still about 7.65 M for the asserter and 0.94 M for the challenger.

The rest of this section is the measurement of 2026-09-17, on the zkboo 1.2.1 circuit; its figures differ from these by less than 0.1%.

Measured on 2026-09-17 in revm under Osaka rules, on the 219-response hardened-child lift, Fast profile, with the contracts as they stand after the residual rewrite, the resumable fold and the split calldata copies (`fixtures/optimistic-*-2026-09-17-margin.summary.log`; the fuzz campaign, which does not depend on them, is `fixtures/optimistic-fuzz-2026-09-17.summary.log`). Every protocol transaction was sent with a 2^24 gas limit and succeeded, EIP-7623's calldata floor included.

### Once per statement

| transaction                     |            gas |
| ------------------------------- | -------------: |
| code store contract             |        175,047 |
| lift bytecode, 3 chunks         |     11,649,315 |
| matrix bytecode, 3 chunks       |     11,768,102 |
| one-step contract               |      4,284,122 |
| lift jump table, built on chain |      7,311,516 |
| matrix jump table               |      7,529,049 |
| dispute contract                |      2,007,491 |
| **in all, 11 transactions**     | **44,724,642** |

The largest single transaction, the matrix program's jump table, uses 45% of the cap.

### Per lift, unchallenged

| transaction                         |            gas |
| ----------------------------------- | -------------: |
| lift upload, 7 transactions         |     48,378,251 |
| matrix proof upload, 4 transactions |     14,918,583 |
| `assertLift`                        |        297,132 |
| `confirm`, after the window         |         84,011 |
| **in all, 13 transactions**         | **63,677,977** |

- **Uploads.** The uploads are 99.4% of the cost, almost all of it EIP-7623's calldata floor.
- **Assertion and confirmation** alone cost 381,143 gas.
- **Blobs.** The 1,652,672 proof bytes would fit 14 blobs at 31 bytes per field element. Their cost is the blob fee market's, which is not modelled here. A disputed blob word would be opened with at most two KZG point evaluations, 50,000 gas each, measured at 73,688 gas for a whole transaction making one.
- **Against direct verification.** Staged direct verification is 889.0 M gas in 106 transactions, so the unchallenged path costs about a fourteenth of it, in 13 transactions.

### Per dispute

The valid trace is **237,058,466 steps**: 134,146,190 in the lift call and 102,912,276 in the matrix call. A lift whose middle byte is flipped is rejected after 26,663,976 steps. A matrix proof whose middle byte is flipped is rejected after 203,601,112 steps, inside the matrix call.

| arity | dissections | dissect gas | choose gas | both sides, all |
| ----: | ----------: | ----------: | ---------: | --------------: |
|     2 |          28 |      85,220 |     66,002 |       4,234,216 |
|     4 |          14 |      86,792 |     73,502 |       2,244,116 |
|    16 |           7 |      96,202 |     84,569 |       1,265,397 |
|    64 |           5 |     133,890 |    128,882 |       1,313,860 |
|   256 |           4 |     347,710 |    348,060 |       2,783,080 |
|  1024 |           3 |   1,327,780 |  1,328,130 |       7,967,730 |

The simulation used arity 16 (`fixtures/optimistic-dispute-sim-2026-09-17-margin.summary.log`):

| transaction (arity 16) | min gas |   max gas |
| ---------------------- | ------: | --------: |
| `challenge`            | 207,213 |   224,313 |
| `dissect` (15 hashes)  |  88,022 |    99,038 |
| `choose`               |  51,704 |    87,405 |
| `resolve`              | 145,995 | 6,960,415 |
| `timeout`              |  51,224 |   108,090 |

- **The heaviest step** is the `KECCAK256` that folds the matrix proof's 9,474 counts into the transcript, 4,739 words, at step 59,122,327 of the matrix call. Its witness proves those 4,739 memory words.
  - On its own it costs 6,788,318 gas as a transaction to `OneStep` (`fixtures/optimistic-onestep-check-2026-09-17-margin.summary.log`).
  - **Resolved inside a game it costs 6,960,415 gas, 41% of the cap, with 9.82 M to spare.**
  - **Copies.** The verifier's transcript now copies calldata in pieces of at most 16,384 bytes. The copy that used to be heaviest, the same counts moved in one `CALLDATACOPY` (9,476 words proved, 14.84 M resolved), is gone, and no copy step checked costs more than 2.56 M.
  - **Zero-filling.** The residual and fold buffers are no longer zero-filled on allocation, which would otherwise add copies of 5,000 to 9,000 words.
  - The trace statistics bound the witness of every one of the 237 million steps, and none needs more words (`fixtures/optimistic-trace-2026-09-17-margin.summary.log`).
- **Worst case per side**, at arity 16:
  - **Asserter:** 7 dissections, 693,266 gas, plus a resolution of at most 6,960,415. **About 7.65 M gas.**
  - **Challenger:** the challenge and 7 choices, 836,148 gas, plus a timeout of 108,090 when the asserter cannot resolve. **About 0.94 M gas**, and it never has to resolve a step itself.
- **Duration.** A full dispute is 14 moves and a resolution, each within a move time: about 15 days at one day per move.

### Off-chain work

- **Replay.** Replaying both calls under revm with the step hook takes about 1.1 s at about 210 million steps per second, and counting the trace took 1.4 s.
- **Rounds.** A round's truth pass for all 16 games took 2.2–2.8 s, and building the final steps' witnesses 2.0 s.
- **Whole simulation.** The 16-game simulation, with its 197 moves and 14 resolutions, ran in 23.5 s at 1.9 GB peak memory, including building the block and the entry-list key.
- **No re-proving.** An asserter or a watcher needs the lift, the statement and revm, not the prover.

### Before the port

The first prototype, on 2026-09-16 (`fixtures/optimistic-*-2026-09-16.summary.log`), disputed the previous direct route: the lift contract, then `FlockDischarge`'s Keccak part, its whole row stream, and its final check.

| figure                     | four-call route, 2026-09-16 | two-call route, 2026-09-17 | current contracts |
| -------------------------- | --------------------------: | -------------------------: | ----------------: |
| trace                      |              49,070,979,080 |                393,389,144 |       237,058,466 |
| dissections at arity 16    |                           9 |                          8 |                 7 |
| heaviest resolution        |                    3.98 M * |                    14.84 M |            6.96 M |
| worst dispute, asserter    |                    4.87 M * |                    15.63 M |            7.65 M |
| worst dispute, challenger  |                    1.12 M * |                     1.03 M |            0.94 M |
| unchallenged path          |             48.7 M in 9 txs |           63.7 M in 13 txs |  63.7 M in 13 txs |
| deployment                 |            44.7 M in 10 txs |           72.7 M in 13 txs |  44.7 M in 11 txs |
| a whole dispute, off chain |                about 50 min |                 about 40 s |        about 25 s |

The figures marked \* were derived from a measured step plus a measured bookkeeping overhead, while the new figures were resolved inside a game.

The two-call route was 125 times shorter and needed only a matrix proof upload instead of a pinned row stream, at the price of a heavier worst step, as the matrix contract copied more of its calldata at once. The current contracts (`fixtures/optimistic-*-2026-09-17.summary.log` held the middle column's figures) shorten the trace by 40% with the residual rewrite, and halve the worst step by copying calldata in pieces.

## Evidence that it works

- **The one-step contract agrees with revm on the real trace.** `onestep-check` covered 50,432 steps of the 219-response verification on the current contracts (42,635 on the previous ones), with zero mismatches:
  - the first step at every program counter of both calls;
  - 300 random steps per call;
  - both call-ending steps, including the one that builds the matrix call from the claims and the on-chain digest;
  - the steps with the largest witnesses.

  For each, the contract's hashes of the states before and after equal those of the states revm went through.
- **It agrees with revm on random programs, including the steps that halt them.** `onestep-fuzz` ran 21,000 random programs, 1,011,852 steps over 111 distinct opcodes, 22,570 of them rejecting (stack underflow, bad jumps, `REVERT`, `INVALID`, foreign calls, oversized memory, unsupported opcodes), with zero mismatches (`fixtures/optimistic-fuzz-2026-09-17.summary.log`).
  - **Coverage.** Each program runs as either call, so both the chaining into the matrix call and the final accept rule are checked.
  - **Bugs found earlier.** The 2026-09-16 campaigns found two bugs, both fixed then: `addmod`/`mulmod` with a zero modulus, and an overflowing return-data bound.
- **Forged witnesses are refused.** A test flips bytes in the memory and calldata proofs of real steps, and every forgery makes the step revert or change its result.
- **Every game ends with the truthful side winning.** This holds for all 16 games on the real lift at arity 16, and on stand-in contracts at arities 2 and 16 (`cargo test`, in seconds):
  - the asserter lies from the first step, inside the lift call, at its return, inside the matrix call, at the last state;
  - it claims one step too few;
  - it asserts a tampered lift, truthfully until the failing check or with a trace cut short at it;
  - it asserts a tampered matrix proof, truthfully until the failing check;
  - an honest asserter meets a challenger that always picks the last interval, or picks at random;
  - either side stops moving;
  - three games are forced to end at the three heaviest steps, each resolved under the cap.
- **The state commitments and the digest are shared.** The same first state is computed on chain by `assertLift`, the digest included, and off chain from revm's run. The games that end at step 0, and those that end at the lift call's return, would fail if either differed.

## Assumptions

These are parameters of the prototype, not measurements:

| parameter        | value used | what it trades                                |
| ---------------- | ---------: | --------------------------------------------- |
| bond, each side  |    1 ether | must cover a side's worst-case dispute gas    |
| challenge window |     7 days | acceptance latency against watchers' reaction |
| time per move    |      1 day | a dispute can last about 15 days              |
| dissection arity |         16 | gas per move against the number of moves      |

What the protocol assumes of the world:

- **An honest watcher** checks every assertion and challenges a false one within the window.
- **Liveness and inclusion.** Both sides get transactions included within each move time. A censor able to delay one side's transactions for a move time wins that side's game.
- **Data availability.** The uploads' calldata is retrievable from chain history for as long as a dispute can last. Nodes that prune history (EIP-4444) do not provide it, so a watcher needs an archive or its own copy. A blob-based upload would bound the window by blob retention, about 18 days, only a few days above the dispute length.
- **The statement's contracts are the audited ones.** A relying party compares `OneStep.codeHash(0)` and `codeHash(1)` with the audited `FlockLift` and `FlockMatrix`, and checks the pinned values `OneStep` exposes.
- **Revm is the reference.** The machine is defined by `OneStep`. Revm generates the traces, and the two are shown to agree by the checks above, not by proof.

## Adversarial review

- **Equivocation.** The asserter's hashes are fixed per move by a commitment that the challenger's move must reopen. To be confirmed, an assertion must survive every game, and in each game an honest challenger wins whenever the claimed end state is false. Lying about an intermediate state loses even when the final claim is true.
- **Stalling.** Every move has a deadline, and the side that misses it loses. That includes the asserter at the final step, where the burden of resolution lies. Challengers can only delay confirmation, and each pays a bond to do so.
- **Binding.**
  - **Initial state.** It is computed on chain from the upload roots, which the contract computes itself, from the statement's output, word counts and binding, from the lift's own header, and from the statement and code pinned in `OneStep`.
  - **Digest.** It is derived on chain as the lift contract derives it, so an asserter cannot pair a lift with a matrix proof made under another lift's transcript domain.
  - **The matrix call's calldata** is built at the lift call's return from the returned claims.
  - **Witnesses.** A step's witness is checked against the pre-state's roots, and unused proofs revert the step.
- **Heavy steps.** The valid lift's heaviest step resolves at 6.96 M gas, so an honest asserter can always resolve under the cap, with 9.82 M to spare. A malicious proof could steer the verifier into a step too large to prove. That only hurts the side that must resolve it, and the burden is the asserter's, so a false assertion cannot hide behind such a step. An honest asserter asserts only valid proofs, whose traces have the shape measured here.
- **Griefing.**
  - **Cost of a groundless challenge.** A challenger who disputes a true assertion loses its bond. Each such game still costs the asserter up to about 7.7 M gas, which the bond must cover.
  - **Off-chain effort.** One truth pass per round serves all open games at once, so many challengers cost the asserter little computation.
  - **Prize race.** The first winning challenger takes the asserter's bond. That is an incentive question, not a soundness one.
- **Departures from the EVM.** Each departure can only reject. The only way one could turn a rejection into acceptance is if the verifier's control flow depended on gas, and it does not.

## What remains before deployment

- **The heaviest step's margin.** Done: the worst resolution is 6.96 M of the 16.78 M cap. The largest remaining witness is the transcript's fold of the matrix counts, which only a change to the transcript itself (hashing its pending bytes in pieces, prover included) would shrink.
- **Timing and economics.**
  - Chess clocks instead of per-move deadlines.
  - Bond sizing against gas prices.
  - Rewards shared among concurrent challengers.
  - A minimum challenge period that survives censorship.
- **Data availability.** Either a blob-based upload with a data-availability sub-game, or an explicit history-retention assumption.
- **Assurance of the one-step contract.** An audit, and more than differential testing.
- **Integration.** A statement registry, the relying party's checks, and the ERC-4337 account that consumes `accepted`.
- **Latency.** Acceptance takes at least the window, and a dispute can extend it by about as long again. Whether that suits an emergency migration is a decision for the project. Direct verification has no such delay, and now runs in 106 transactions under the cap (`staged-verification.md`).
