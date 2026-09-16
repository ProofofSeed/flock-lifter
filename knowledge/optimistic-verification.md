# Optimistic verification of a Flock lift

Status: prototype on its own branch, 2026-09-16; not merged.
A lifted proof can be accepted on Ethereum without being verified there, unless someone disputes it: an asserter uploads the proof, asserts that the verification accepts, and posts a bond, and any disagreement is settled by narrowing it to one EVM step, which a contract re-executes.
This record says what was built, what it costs as measured on the 219-response hardened-child lift, what establishes that it works, and what it assumes.

## What is asserted

The asserted computation is the existing verifier: the `FlockLift` contract, then `FlockDischarge`'s Keccak part, its whole stream in one segment, and its final check (`evm-verifier.md`).
The machine is the EVM running that bytecode as four chained calls, each later call's calldata built from earlier outputs.
It departs from the EVM in four ways, and each can only turn an accepting run into a rejecting one:
- `GAS` pushes 2^32;
- the only callable address is the SHA-256 precompile;
- memory is capped at 2^22 words (134 MB);
- any opcode outside the implemented set rejects, as do reverts and every exceptional halt.

On the valid 219-response lift, none of these departures is ever hit. The trace has no unsupported opcode and no call outside SHA-256, and peak memory is 24.3 MB. The verifier's only use of `GAS` is as the gas argument of its two SHA-256 calls.

A state commits to:
- the call and the program counter;
- the stack;
- memory, as a Keccak Merkle tree of depth 22 over its words, with its size;
- the return data;
- the call's context.

The context commits to:
- the calldata, as a selector, a prefix tree of depth 10 and a body tree of depth 24;
- the hashes of the earlier calls' outputs.

The body of the first call is the uploaded proof, and the body of the stream call is the discharge stream, whose root is pinned per statement. Accepting and rejecting states are terminal and absorb further steps, so a trace of any claimed length is well defined.

## The protocol

1. **Deployment, once per statement.**
   - The runtime bytecode of the statement's `FlockLift` and `FlockDischarge` goes into data-holding contracts, in 24 KB chunks. `FlockLift` is 87 KB, which is over EIP-170's limit for an executable contract, but it never has to run.
   - `OneStep` computes each program's jump-destination bitmap on chain.
   - `Dispute` is deployed with a bond, a challenge window, a time per move and a dissection arity.
2. **Upload.** The asserter sends the 1,215,008 proof bytes in 262,144-byte chunks. The contract hashes each chunk into a subtree root and combines them into the root of the depth-24 word tree. The bytes themselves stay available as transaction calldata.
3. **Assertion.** `assertLift(output, counts, binding, upload, steps)` takes the bond. It computes the machine's initial state on chain from the statement and the upload root, and records the claim that state `steps` is the accepting terminal.
4. **Challenge.** Anyone may challenge within the window, with the same bond. Each challenge is a separate game over the interval `[0, steps]`.
5. **Dissection.**
   - The asserter posts the state hashes at the `k − 1` interior points of the current interval.
   - The challenger names a sub-interval.
   - This repeats until the interval is one step. Each side has one move time per move.
6. **Resolution.** Anyone may call `resolve` with the agreed state's preimage and the step's witness: memory and calldata range proofs, and at a call boundary the earlier outputs. `OneStep` re-executes the step, and the challenger wins unless the result is the asserter's state.
   - The burden is on the asserter: if nobody resolves in time, the challenger wins.
   - Whoever lets a move time run out loses.
7. **Settlement.** A winning challenger takes its bond back, plus the asserter's bond if it is the first to win. A winning asserter takes the challenger's bond. After the window, an assertion with no open or lost game is confirmed, its bond is returned, and its statement reads as accepted.

## Firm numbers

Measured in revm under Osaka rules. Every protocol transaction was sent with a 2^24 gas limit and succeeded, EIP-7623's calldata floor included.

### Once per statement

| transaction                     |            gas |
| ------------------------------- | -------------: |
| code store contract             |        175,047 |
| lift bytecode, chunk 0          |      5,241,380 |
| lift bytecode, chunk 1          |      5,244,884 |
| lift bytecode, chunk 2          |      5,243,888 |
| lift bytecode, chunk 3          |      3,300,794 |
| discharge bytecode              |      4,929,147 |
| one-step contract               |      4,291,630 |
| lift jump table, built on chain |     11,521,871 |
| discharge jump table            |      2,818,643 |
| dispute contract                |      1,958,431 |
| **in all, 10 transactions**     | **44,725,715** |

The largest, the lift's jump table, uses 69% of the cap.

### Per lift, unchallenged

From `dispute-costs`, on the proof itself (`fixtures/optimistic-dispute-costs-2026-09-16.summary.log`):

| transaction                    |            gas |
| ------------------------------ | -------------: |
| `beginUpload`                  |         88,237 |
| upload chunk 0 (262,144 bytes) |     10,166,780 |
| upload chunk 1                 |     10,472,780 |
| upload chunk 2                 |     10,449,200 |
| upload chunk 3                 |     10,474,850 |
| upload chunk 4 (166,432 bytes) |      6,645,530 |
| `finishUpload`                 |         82,494 |
| `assertLift`                   |        259,601 |
| `confirm`, after the window    |         83,989 |
| **in all, 9 transactions**     | **48,723,461** |

- **The upload is 99% of it,** and almost all of that is EIP-7623's calldata floor: about 40 gas per byte for data-heavy transactions.
- **Assertion and confirmation alone are 343,590 gas.** That is what the asserter pays if the proof is made available some other way.
- **Blobs.** The proof fits 10 blobs at 31 bytes per field element. Their cost is the blob fee market's, which is not modelled here. A dispute over the data would open a word with at most two KZG point evaluations: 50,000 gas each by EIP-4844, measured at 73,652 gas for a whole transaction making one.

### Per dispute

The valid trace is **49,070,979,080 steps**. Per call:

| call          |          steps |
| ------------- | -------------: |
| lift contract |    257,254,596 |
| Keccak part   |    323,757,884 |
| stream        | 48,473,269,630 |
| final check   |     16,696,970 |

The asserter must name that count, and the tampered proof's trace ends after 26,649,123 steps.

One move, and the moves a dispute over the whole trace takes, at each arity (`dispute-costs`; the "in all" column is both sides' dissections and choices over a whole dispute):

| arity | dissections | dissect gas | choose gas |     in all |
| ----: | ----------: | ----------: | ---------: | ---------: |
|     2 |          36 |      85,220 |     66,002 |  5,443,992 |
|     4 |          18 |      86,792 |     73,502 |  2,885,292 |
|    16 |           9 |      96,202 |     84,569 |  1,626,939 |
|    64 |           6 |     133,890 |    128,882 |  1,576,632 |
|   256 |           5 |     347,710 |    348,060 |  3,478,850 |
|  1024 |           4 |   1,327,780 |  1,328,130 | 10,623,640 |

The simulation used arity 16 and made 9 dissections in every game played over the whole trace.

| transaction (arity 16, simulation) | min gas | max gas |
| ---------------------------------- | ------: | ------: |
| `challenge`                        | 207,191 | 224,291 |
| `dissect` (15 hashes)              |  88,022 |  99,038 |
| `choose`                           |  51,704 |  87,381 |
| `resolve`                          | 142,010 | 793,661 |
| `timeout`                          |  51,224 | 108,090 |

- **The heaviest step anywhere in the trace** is an `MCOPY` of 3,200 words in the Keccak part. It costs 3,952,605 gas as a transaction to `OneStep`, witness calldata included. The trace statistics show no step needs more words, over all 49 billion steps (`fixtures/optimistic-trace-2026-09-16.summary.log`).
- **Resolution overhead.** `resolve` adds about 27,000 gas of game bookkeeping, measured on the call-boundary step (766,869 alone, 793,661 resolved). So **the worst resolution is about 3.98 M gas, a quarter of the cap.**
- **Worst case per side**, at arity 16:
  - **Asserter:** 9 dissections at most, 891,342 gas, plus a resolution of at most about 3.98 M. **About 4.87 M gas.**
  - **Challenger:** the challenge and 9 choices, 1,010,720 gas, plus a timeout of 108,090 when the asserter cannot resolve. **About 1.12 M gas**, and it never has to resolve a step itself.
- **Duration.** A full dispute is 18 moves and a resolution, each within a move time: about 19 days at one day per move.

### Off-chain work

Measured on this machine, while another session's jobs shared it at times (`fixtures/optimistic-dispute-sim-2026-09-16.summary.log`):

- **Replaying the verification** under revm with the step hook takes 190–320 s, almost all of it the stream call: 48.5 billion steps at 150–270 million steps per second. Counting the trace took 319 s.
- **One round of a dispute** is one replay that stops at the dissection points and builds their memory trees (up to 24.3 MB of memory, 760,000 words). It took 285–324 s for all 13 games at once, and building the final steps' witnesses took one more pass of 285 s.
- **A whole dispute is therefore about 50 minutes** of one core, however many games run in parallel. The 13-game simulation took 3,306 s at 2.8 GB peak memory.
- **The proof itself** is not re-proved: an asserter and a watcher need only the lift and revm.
- **The stream's word tree** (7.45 M words) is built once per statement, and the proof's tree once per upload.

## Evidence that it works

- **The one-step contract agrees with revm on the real trace.** `onestep-check` covered 36,631 steps of the 219-response verification: the first step at every program counter of every call, 300 random steps per call, every call-ending step, and the steps with the largest witnesses. For each, the contract's hashes of the state before and after equal those of the states revm went through, with zero mismatches (`fixtures/optimistic-onestep-check-2026-09-16.summary.log`). This covers every instruction instance the verifier executes, and the glue between calls.
- **It agrees with revm on random programs, including the steps that halt them.** `onestep-fuzz` ran 21,000 random programs over 111 distinct opcodes: 1,034,834 steps, 22,519 of them rejecting (stack underflow, bad jumps, `REVERT`, `INVALID`, foreign calls, oversized memory, unsupported opcodes). There were no mismatches (`fixtures/optimistic-fuzz-2026-09-16.summary.log`). Its first campaigns found two bugs that the real trace never reached, both fixed: Solidity's checked `addmod`/`mulmod` reverted on a zero modulus where the opcode returns 0, and the return-data bound overflowed.
- **Forged witnesses are refused.** A test flips bytes in the memory and calldata proofs of real steps, and every forgery makes the step revert or change its result.
- **Every game ends with the truthful side winning,** on the real lift at arity 16 and on stand-in contracts at arities 2 and 16 (`cargo test`, a few seconds):
  - the asserter lies from the first step, at the lift call's return, inside the Keccak part, in the middle of the stream, inside the final check, at the last state;
  - it claims one step too few;
  - it asserts a tampered proof, either truthfully until the failing check or with a trace cut short at it;
  - an honest asserter meets a challenger that always picks the last interval, or picks at random;
  - either side stops moving.
- **The state commitments are shared.** The same hash of the machine's first state is computed on chain by `assertLift` and off chain from revm's run, and the games that end at step 0 would fail if they differed.

## Assumptions

These are parameters of the prototype, not measurements:

| parameter        | value used | what it trades                                |
| ---------------- | ---------: | --------------------------------------------- |
| bond, each side  |    1 ether | must cover a side's worst-case dispute gas    |
| challenge window |     7 days | acceptance latency against watchers' reaction |
| time per move    |      1 day | a dispute can last about 19 days              |
| dissection arity |         16 | gas per move against the number of moves      |

What the protocol assumes of the world:
- **An honest watcher** checks every assertion and challenges a false one within the window.
- **Liveness and inclusion.** Both sides get transactions included within each move time. A censor able to delay one side's transactions for a day wins that side's game.
- **Data availability.** The upload's calldata is retrievable from chain history for as long as a dispute can last. Nodes that prune history (EIP-4444) do not provide it, so a watcher needs an archive or its own copy. A blob-based upload would bound the window to blob retention, about 18 days.
- **The statement's contracts are the audited ones.** `OneStep.codeHash(which)` returns the hash of the held bytecode for a relying party to compare. The stream root is pinned at deployment: a wrong one makes every run reject, which is a liveness failure, not a soundness one.
- **Revm is the reference.** The machine is defined by `OneStep`; revm generates the traces, and the two are shown to agree by the checks above, not by proof.

## Adversarial review

- **Equivocation.** The asserter's hashes are fixed per move by a commitment the challenger's move must reopen. Hashes posted in different games are independent. To be confirmed, an assertion must survive every game, and in each game an honest challenger wins whenever the claimed end state is false. Lying about an intermediate state loses even when the final claim is true: the simulation's "lie at the last state" game shows it.
- **Stalling.** Every move has a deadline, and the side that misses it loses, including the asserter at the final step, where the burden of resolution lies. A dispute therefore ends within a bounded time. Challengers can only delay confirmation, by the dispute length after the last challenge, and each pays a bond to do so.
- **Binding.** The initial state is computed on chain:
  - from the upload root, which the contract computes itself;
  - from the statement's output, word counts and binding, which enter the lift call's calldata commitment;
  - under the program code and stream root pinned in `OneStep`.

  Later calls' calldata is derived on chain from earlier outputs, which a boundary step re-hashes. A step's witness is checked against the pre-state's roots, and unused memory or calldata proofs revert the step; earlier outputs are read only at a call boundary, where they are checked against the context's hashes.
- **Heavy steps.** On the valid lift the heaviest step needs 3.95 M gas, so an honest asserter can always resolve under the cap. A malicious proof could steer the verifier into a step too large to prove. That only hurts the side that must resolve it, and the burden is the asserter's, so a false assertion cannot hide behind such a step. An honest asserter only asserts valid proofs, whose traces have the shape measured here.
- **Griefing.**
  - **Cost to the asserter.** A challenger who disputes a true assertion loses its bond. Each such game costs the asserter about 0.87 M gas in dissections at arity 16, plus a resolution of at most about 4 M gas, which the bond must cover.
  - **Off-chain effort.** One truth pass per round serves all open games at once, as the simulation does, so many challengers cost the asserter little more computation than one.
  - **Prize race.** The first winning challenger takes the asserter's bond, so honest challengers race for it. That is an incentive question, not a soundness one.
- **Departures from the EVM.** Each departure can only reject. The only way one could flip a rejection into acceptance is if the verifier's control flow depended on gas, and it does not.

## What remains before deployment

- **Timing and economics.**
  - Chess clocks instead of per-move deadlines.
  - Bond sizing against gas prices and off-chain effort.
  - Rewards shared among concurrent challengers.
  - A minimum challenge period that survives censorship.
- **Data availability.** Either a blob-based upload with a data-availability sub-game, or an explicit history-retention assumption. A disputed blob word would be settled with at most two point evaluations at 50,000 gas each (measured).
- **Assurance of the one-step contract.** An audit, and more than differential testing: a proof of equivalence to the EVM for the implemented opcodes, or a second independent implementation.
- **Integration.**
  - A statement registry.
  - The relying party's check of `codeHash` and of the confirmed statement.
  - The ERC-4337 account that consumes `accepted`.
- **Latency.** Acceptance takes at least the window, days, and a dispute can extend it by about as long again. Whether that suits an emergency migration is a decision for the project, not a measurement.
