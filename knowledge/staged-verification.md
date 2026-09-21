# Staged verification under mainnet limits

Status: built and measured, 2026-09-17; re-measured on zkboo 1.3.0, 2026-09-21.
The direct route now runs on Ethereum as it is. Every transaction fits the 2^24-gas cap (EIP-7825), and every deployed contract fits the 24,576-byte code-size limit (EIP-170).
Verifying the 219-response hardened-child lift takes **889.04 M gas in 106 transactions** under the `Fast` profile, and 780.85 M in 100 under `Slim`, against a one-off deployment of 30.74 M (zkboo 1.3.0, `fixtures/evm-bench-2026-09-21-zkboo-1.3.0-{fast,slim}.summary.log`).
The matrix proof can only be checked against claims that a verified lift recorded.

The single-call contracts (`FlockLift`, `FlockMatrix`, `committed-matrix.md`) are kept in two roles. They are the reference the staged verifier is checked against, and the program the optimistic route disputes (`optimistic-verification.md`). They are never deployed to run: at 53 KB each they are still over the limit.

## Design

**Sessions.** `FlockSessions` holds one hash per open session: the Keccak-256 of that session's current state.
- **Advancing.** A caller advances its session with the current state, an item bound `upto` and the proof bytes the call reads. The session contract checks the state against the hash, routes the call by stage number to a stage contract, and records the hash of the state that comes back.
- **Scope.** A session belongs to its caller: its id is the hash of the sender and a salt.
- **Stage contracts.** They are stateless `view` functions, so every step is deterministic and the only trust anchor is the chain of state hashes.

**Binding the two calls.**
- **Lift end.** The lift session's last stage runs the Fiat-Shamir gate and returns the statement digest with the hash of the packed matrix claims. The session contract records the pair (`liftClaims`).
- **Matrix start.** `startMatrix` takes a digest and claims, and refuses them unless their hash is the recorded one. The digest the matrix transcript starts from is therefore one a lift session derived on chain from the statement, where the single-call route took it as an argument.
- **Acceptance.** The matrix session ends by setting `accepted[digest]`.

**State.** A state is its stage number followed by an ABI-encoded bag (`staged/Staged.sol`):
- named scalars;
- named arrays: claims, level challenges, stratified queries, caps, the ring-switch tensor's columns, the structured fold's kernel and so on;
- the transcript, as its chaining value and pending bytes.

The state is 8 to 57 KB at 219 responses, 4.2 MB over the whole verification, and carrying it costs up to 0.7 M gas of calldata per transaction. Arrays a later stage no longer needs are emptied, and the fold's kernel is packed two 128-bit values a word.

**Streams.** Each stage returns, with the next state, what the next call must read: per stream, a source (the proof, the expected output or the binding), a base and either a per-item unit, a fixed length or "what the stage consumes".
- **Driver.** `crates/evm/src/staged.rs` is generic over this. It offers a sequential stage a window and learns where its read ended. For an itemised stage, it finds by simulation the largest item range that fits the cap, then commits that call.
- **Unbound bytes.** Proof bytes that no transcript absorbs and no cap binds are bound across calls by hash. These are the published words (one hash per chunk, and one over the gate's whole region), the matrix counts (two hashes, taken where they are first read), and the prefix-count rows (a per-row hash chain, compared at the end with the chain of the absorbed counts).

## Stages

| stage                | contract            | items                                  |
| -------------------- | ------------------- | -------------------------------------- |
| published words      | `LiftStages`        | 1                                      |
| chunk PIOP           | `LiftStages`        | 1                                      |
| published-word claim | `LiftTailStages`    | rows                                   |
| ring switches        | `OpeningStages`     | 1                                      |
| Ligerito rows        | `OpeningStages`     | queries of one level                   |
| Ligerito level       | `OpeningStages`     | 1                                      |
| final message        | `OpeningStages`     | 1                                      |
| out-of-domain part   | `OpeningStages`     | 1                                      |
| ring-switch residual | `RingSwitchStages`  | per claim: rank, steps, suffix points  |
| consistency residual | `ConsistencyStages` | per level: prefix factors, suffix form |
| chunk final check    | `LiftTailStages`    | 1                                      |
| Fiat-Shamir gate     | `LiftTailStages`    | 1                                      |
| structured parts     | `StructuredStages`  | 26 per claim: setup, 24 rounds, last   |
| main sumcheck        | `MatrixStages`      | 1                                      |
| main check           | `MatrixStages`      | 9 per claim                            |
| counts               | `MatrixStages`      | 1                                      |
| prefix counts        | `MatrixStages`      | 128 rows                               |
| count sumcheck, bits | `MatrixStages`      | 1                                      |

The opening, residual and check stages are shared by the lift's chunks and the matrix proof. The code is that of the single-call verifier, cut at loop boundaries.
- **Rows.** A level's rows are checked against its cap query by query, with column sums carried in the state and batched when the level ends. The sums use Horner tables with 8-bit windows.
- **Structured fold.** The Keccak fold's kernel is carried between rounds. `Structured` gained modes that set the fold up, fold a range of rounds and make the last pairing, and fill only the `eq` entries those rounds read.

## Code size

| contract            | runtime (B) | deployment (M gas) |
| ------------------- | ----------: | -----------------: |
| subspace table      |      12,289 |               2.64 |
| `LiftStages`        |      22,893 |               5.00 |
| `LiftTailStages`    |      15,368 |               3.38 |
| `OpeningStages`     |      22,674 |               4.96 |
| `RingSwitchStages`  |      14,768 |               3.25 |
| `ConsistencyStages` |      13,427 |               2.96 |
| `MatrixStages`      |      21,318 |               4.66 |
| `StructuredStages`  |      12,171 |               2.68 |
| `FlockSessions`     |       3,189 |               1.22 |

What made them fit:
- **Schedules.** The Ligerito schedules are generated as a 1 KB byte table with a decoder (`evm-constants`), instead of twelve functions of array writes. That alone took the single-call contracts from 103 KB to 53 KB.
- **Subspace table.** `Constants.SUBSPACE` (12 KB) lives in a data contract, a leading `STOP` then the bytes, and `ConsistencyStages` reads it with `EXTCODECOPY`.
- **Splits.** The lift and residual stages are split in two contracts each.
- **Statement parameters.** `LiftStages` and `MatrixStages` carry them as immutables, like the single-call contracts. The other five contracts are shared by any statement.

## What it costs

`evm-bench 219`, both profiles, on the zkboo 1.2.1 circuit (`fixtures/evm-bench-2026-09-17-staged-fast.summary.log`, `-slim.summary.log`); gas in millions, calldata included. On zkboo 1.3.0 the totals are 889.04 M (`Fast`) and 780.85 M (`Slim`) in the same numbers of transactions, and no session moves by more than 0.4 M (`zkboo-1.3.0-migration.md`):

| session     | transactions, `Fast` | gas, `Fast` | transactions, `Slim` | gas, `Slim` |
| ----------- | -------------------: | ----------: | -------------------: | ----------: |
| lift        |                   63 |      464.72 |                   59 |      383.35 |
| matrix      |                   43 |      424.24 |                   41 |      397.64 |
| **in all**  |              **106** |  **888.96** |              **100** |  **780.99** |
| single call |        (46 at least) |      758.95 |        (39 at least) |      648.79 |

Largest transaction: 16.57 M against a cap of 16.78 M.

**Where the 130 M over the single call goes** (`Fast`):
- **Structured parts** (193 M in 12 transactions, against 142 M). Each call rebuilds 64 pairing tables, fills the `eq` entries it needs, and pays memory expansion for about half a megabyte of tables and a 54 KB state. That is about 4 M a call, where one round costs about 2.4 M.
- **The matrix main check** (65 M against 42 M). Every call carries the 152 KB of counts (1.6 M of calldata) and rebuilds the prefix table's suffix sums.
- **State calldata** in every transaction, about 30 M in all. The lift's rows cost 25 M of calldata, which the single call also paid.
- **The lift's residuals.** They pay per-call table builds, about 25 M more than the single call.

`Structured` itself got cheaper for the single call too. Its buffers are no longer zero-filled, and its skip-weight tables use 4-bit windows, which took the tables from 1 MB to 573 KB. That cost 0.34 M more fold work per claim and saved about 2 M of memory expansion wherever an allocation follows the tables.

## Validation

`crates/evm/tests/staged.rs`, on an 8-response lift in two chunks, deploys every contract under the limit and runs the whole verification under the cap. It then checks:
- **Refusals.**
  - A tampered lift is refused (at the Ligerito rows), and so is a tampered matrix proof (at the main check).
  - `startMatrix` refuses forged claims and an unrecorded digest.
  - `advance` refuses a well-formed state other than the recorded one, and a session that was never opened.
- **Agreement.** The recorded claim hash equals the hash of the single-call lift contract's output, and the matrix session ends in acceptance.
- **Deletion.** With the claim check or the state-hash check deleted, the test fails at the matching assertion (`fixtures/deletion-validation-2026-09-17-staged-sessions.summary.log`).
- **Structured pieces.** `crates/evm/tests/structured.rs` checks that the structured value computed across fresh buffers at various round cuts equals the value computed whole.

`evm-bench` repeats the claim-hash check at 219 responses under both profiles.

## Limits

- **Trust.**
  - The session contract, the stage routing and the state layout are new code, tested and validated as above but not audited.
  - Anyone can open a session, and a session only advances from its opener's address. So one opener's failure or abandonment cannot block another's verification of the same lift.
  - A lift is recorded by digest, and any successful session sets the same record.
- **Cap margin.** The driver packs each transaction to the cap: the largest is 16.57 M against 16.78 M. A client must leave its own margin, for example by aiming lower. The item ranges would then shrink and the transaction count grow a little.
- **Transactions and fees.** 106 transactions and 889 M gas amount to about 30 blocks' worth at a 30 M block gas limit. That is feasible, but at a real fee cost.
