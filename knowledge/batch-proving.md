# Batching several proofs of seed in one wrapped lift

Status: investigated, 2026-10-05; nothing built beyond a probe.
The question is how the wrapped lift's costs scale if one lift carried several proofs of seed.
Record: `fixtures/batch-scaling-2026-10-05.summary.log`.

A batch of `k` proofs was stood in for by one proof of more responses, which the lifter already accepts: 219 responses per proof of seed, in chunks of 128.
That exercises every cost but two, which are discussed under Requirements: several statements in one lift, and several Fiat-Shamir gates.

## Findings

- **On-chain gas amortises, down to a floor.** A lift costs about 60 M gas whatever it carries, plus about 23,800 gas per response, plus 1.3 to 2 M each time the number of chunks doubles. A proof of seed therefore adds about 5.2 M to a batch, against 65.85 M alone. Four proofs in one lift measured 87.38 M, 21.8 M each.
- **The floor is the published words.** Almost all of the per-response gas pays for the words each response publishes for the Fiat-Shamir gate: their calldata, their absorption and the gate, and their evaluation in the wiring argument. Moving the gate into the proof would remove it.
- **Proving amortises less.** A proof of seed adds 17 to 29 s to a batch, against 72 s alone, since the chunk proofs and the wrap grow with the batch and only the tables' part is shared. Four proofs took 149.8 s, 37 s each.
- **Memory is the binding limit on this machine.** The committed tables double at four chunks and their commitment no longer fits 137 GB at rate 2^-4. Two proofs fit only with the tables at rate 2^-3, which costs 2.5 M gas.
- **Distinct statements do not batch today.** The committed tables are specific to a statement's chain code and index, so a batch can only repeat one statement until the block takes them as inputs.

## Measurements

Whole lifts, verified by the contract, single call and staged (gas in M):

| responses | chunks | rows a chunk | tables' rate | tables   | single call | staged | lift (s) | peak (GB) |
| --------: | -----: | -----------: | -----------: | -------- | ----------: | -----: | -------: | --------: |
|       219 |      2 |          128 |         2^-4 | 2^27 B   |       65.85 |  68.62 |     72.2 |     123.1 |
|       384 |      3 |          128 |         2^-4 | 2^27 B   |       69.76 |  72.61 |     80.4 |     122.8 |
|       438 |      4 |          128 |         2^-3 | 2^28 B   |       76.57 |  79.65 |    101.4 |     124.2 |
|       657 |      6 |          128 |         2^-3 | 2^28 B   |       82.15 |      — |    132.5 |     122.3 |
|       876 |      7 |          128 |         2^-3 | 2^28 B   |       87.38 |      — |    149.8 |     122.5 |
|         8 |      2 |            4 |         2^-4 | 2^27 B   |       59.45 |  62.03 |     67.0 |     123.2 |
|         8 |      2 |            4 |         2^-3 | 2^27 B   |       61.94 |  64.62 |     39.3 |      72.6 |
|        16 |      4 |            4 |         2^-3 | 2^28 B   |       64.91 |  67.68 |     82.7 |     123.1 |
|        32 |      8 |            4 |         2^-3 | 2^28 B   |       67.35 |  70.19 |    129.0 |     122.9 |

The 438-response row is two proofs of seed in one lift: 38.3 M each in one call, 39.8 M staged.
The 657- and 876-response rows are three and four proofs, 27.4 M and 21.8 M each. They have no staged figure: their first transaction does not fit the gas cap (see Requirements).
With 16 responses in 4 chunks and the tables at rate 2^-4, the lift was killed for memory in the tables' opening.

Chunks and wrap alone, four rows a chunk, tables laid out but not committed (`batch-probe`):

| chunks | live cells | wrap variables | wrap (s) | of which shape | wrap peak (GB) | tables   |
| -----: | ---------: | -------------: | -------: | -------------: | -------------: | -------- |
|      2 |  1,114,019 |             29 |     13.5 |            9.6 |           41.1 | 2^27 B   |
|      4 |  2,223,511 |             30 |     23.9 |           16.3 |           69.2 | 2^28 B   |
|      8 |  4,450,991 |             31 |     57.1 |           42.1 |           82.3 | 2^28 B   |
|     16 |  8,897,454 |             32 |    128.2 |           82.4 |          123.0 | 2^28 B   |

## How the gas scales

Three effects separate cleanly in the measurements.

- **Per response: 23,800 gas.** From 219 to 384 responses at unchanged parameters the single call grows by 3.92 M, 23,700 a response. By stage: 8,300 for binding the published words and running the gate, 10,400 for evaluating them in the wiring argument, 4,000 of calldata, and the rest the third chunk. From 657 to 876 responses the wrap circuit keeps its shape, and the call grows by 5.23 M, 23,900 a response.
- **Per doubling of the chunks: 1.3 to 2 M.** The wrap circuit's rows, cells and committed stack each gain a variable when the batch outgrows a power of two, which lengthens the wiring argument, the layout equation and the outer opening. They do not all step together, so the growth comes in steps and not as a smooth logarithm. From 4 to 8 chunks of four rows, where all three step, the call grows by 2.44 M, of which 0.4 M is its 16 further responses. From 219 to 876 responses in chunks of 128 the steps other than the tables' come to 2.6 M over two doublings.
- **Per step of the tables: 0.7 M for a doubling, 2.5 M for a rate step.** The tables hold a list of the wrap circuit's live cells, about 560,000 a chunk at eight bytes each. That list outgrows the 2^27 bytes at four chunks and 2^28 at about thirty. On this machine each doubling must be paid for with one step of rate.

A model from these, for `k` proofs of seed in chunks of 128, with the tables at rate 2^-3 as this machine needs from two proofs on:

| proofs | responses | chunks | single call (M)  | per proof (M) |
| -----: | --------: | -----: | ---------------- | ------------: |
|      1 |       219 |      2 | 65.85 measured   |         65.85 |
|      2 |       438 |      4 | 76.57 measured   |          38.3 |
|      3 |       657 |      6 | 82.15 measured   |          27.4 |
|      4 |       876 |      7 | 87.38 measured   |          21.8 |
|      8 |     1,752 |     14 | about 110        |      about 14 |
|     16 |     3,504 |     28 | about 156        |     about 9.7 |

The model was written from the rows up to two proofs, with 2 M per doubling.
It then predicted 82.9 M for three proofs and 88.6 M for four, which measured 0.9% and 1.3% lower.
The last two rows extrapolate and have not been run: they are beyond this machine's memory.
As the batch grows the cost per proof tends to 5.2 M, the per-response gas of 219 responses.

## How proving scales

- **Chunk proofs** are linear: 5.2 to 5.8 s a chunk of 128 rows, about 10 s a proof of seed.
- **The wrap** took 16.9 s at two chunks, 19.9 s at three, 31.2 s at four, 49.7 s at six and 53.6 s at seven: it steps with the circuit's shape, and averages about 7 s a chunk. In the four-row sweep two thirds of it is building the circuit's shape, which depends on the batch's shape alone and is rebuilt in every lift.
- **The tables' commitment** takes 10.5 s and is fixed per shape and statement. The prover already accepts a commitment made earlier.
- **The structure proof** takes 33 to 46 s. It steps when the tables double and grows slowly with the live cells.
- **Memory** peaks in the tables' opening, at about 123 GB whenever the codeword has 2^31 symbols. The wrap alone needs 41 GB at two chunks and 123 GB at sixteen, so past eight chunks the outer rate must drop as well.

Two proofs of seed took 101.4 s, against 72.2 s for one: 51 s each. Three took 132.5 s and four 149.8 s: 44 s and 37 s each.
The unwrapped lift takes 13.4 s a proof.

One observation outside batching: with the tables at rate 2^-3 and no change of shape, the lift takes 39.3 s and 72.6 GB where it took 67.0 s and 123.2 GB, for 2.5 M more gas.

## Requirements

- **A key and a deployment per batch size.** The wrap circuit, the committed tables and the contracts' constants are all fixed by the number of responses and the chunk size. A deployment is 35 M gas. A batch short of its size would need padding proofs.
- **A block that takes the statement as input.** The response block is compiled from the statement's public parameters, so the chain code and index are constants of its matrices, and the tables commit to them. Proofs of seed for different parents have different blocks. Either the tables hold one list of operations per statement, 2^24 bytes each and a commitment the contract cannot check, or the block reads the chain code and index as published words. Only the second scales, and it needs the block's compiler to accept inputs that are not witness.
- **A gate per statement.** Each proof of seed has its own binding, expected output and challenge derivation. The on-chain gate would run `k` times over 219 responses, which costs what one gate over `219·k` responses does.
- **An itemised first stage.** The first staged transaction binds every published word and runs the gate. At 438 responses it used 96.1% of the gas cap, and at 657 it no longer fits. Beyond two proofs it has to be split over the responses.

## Routes to better amortisation

None of these is built or measured.

- **The gate inside the proof.** If the wrap circuit hashed the published words and derived the challenges itself, the lift would publish a digest per statement and the 23,700 gas per response would go. A batch would then cost about 60 M plus 1.3 to 2 M per doubling: about 70 M for sixteen proofs, 4.4 M each. The gate hashes about 60 KB per proof with Keccak-256, a two-thousandth of the Keccak work already in a proof's blocks. Flock ships hash tables for BLAKE3 and SHA-2 only, so this needs a Keccak table in the wrap circuit, or the gate inside the block.
- **Recursion.** The vendored Flock carries a recursive step that proves a previous lift and a new wrap verify, folding their deferred claims into accumulators. A chain of such steps would keep the on-chain work and the tables at one wrap's size however many proofs it covered, with the prover working through them in sequence. Its circuit is larger than the wrap's and was not costed.
- **Reusing the wrap circuit's shape.** Building it is about 5 s a chunk in every lift and depends on the batch's shape alone.
