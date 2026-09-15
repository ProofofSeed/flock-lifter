# What everything costs, on this machine

Measured on the machine the SP1 lifter's figures come from: an M4 Max, 16 cores (12 performance, 4 efficiency), 137 GB.
Flock runs on the CPU only, with its NEON kernels and `target-cpu=native`; the SP1 figures it is compared with are on the Metal GPU.
Every row is one process, run one at a time on an otherwise quiet machine, by `lift-bench` under `/usr/bin/time -l`.
Every lift in the table passed verification and the relying-party gate.
The table was first measured on 2026-09-14 (`fixtures/lift-bench-2026-09-14.summary.log`) and re-measured whole on 2026-09-15 with the structured matrix discharge (`fixtures/lift-bench-2026-09-15-structured.summary.log`); only the verify column moved.

## The lift

The statement is the SP1 lifter's: BIP-32 hardened child of test vector 1, Keccak-256 suite, one binding.
"Prove" is the whole lift: laying every response into its block, and the Flock proofs of every chunk.
"Verify" is every chunk's Flock verification, the native Fiat-Shamir gate and the journal.
The ZKBoo proof itself (under 0.2 s at 438 responses) and building the block from the circuit (0.62 s, once per statement) are outside both.

| responses | chunks | threads | prove (s) | verify (s) | was (s) | lifted proof (B) | peak RSS (GB) |
| --------: | -----: | ------: | --------: | ---------: | ------: | ---------------: | ------------: |
|         8 |      1 |      16 |      3.38 |       0.03 |    1.01 |          512,341 |         21.48 |
|        16 |      1 |      16 |      3.98 |       0.03 |    1.02 |          529,597 |         32.10 |
|        32 |      1 |      16 |      4.91 |       0.03 |    1.01 |          549,349 |         54.79 |
|        64 |      1 |      16 |      4.44 |       0.03 |    1.00 |          588,261 |         41.61 |
|       128 |      1 |      16 |      6.52 |       0.04 |    0.98 |          621,933 |         63.59 |
|   **219** |  **2** |  **16** | **12.92** |   **0.06** |    1.97 |    **1,233,478** |     **73.91** |
|       438 |      4 |      16 |     22.91 |       0.10 |    3.95 |        2,451,176 |         78.83 |
|        64 |      1 |      12 |      4.51 |       0.03 |    1.09 |          588,261 |         41.19 |
|       128 |      1 |      12 |      7.34 |       0.03 |    1.03 |          621,933 |         63.19 |
|       219 |      2 |      12 |     14.48 |       0.05 |    2.05 |        1,233,478 |         73.60 |
|       438 |      4 |      12 |     25.52 |       0.08 |    4.18 |        2,451,176 |         78.50 |

Every column is the 2026-09-15 run; "was" is that row's verify time on 2026-09-14, before the structured matrix discharge.
The two runs' prove times agree to within 5% and their proof sizes and peak memory to within a thousandth, which is this machine's run-to-run drift — the matrix discharge is verifier-side only, and a dense-against-structured comparison run back to back on the same day shows no difference in either (`fixtures/matrix-discharge-2026-09-15.summary.log`).

A lift is chunks of at most 128 responses, and each chunk proves a power-of-two number of rows, the last live block repeated as padding.
Within one chunk, prove time is about `3.0 s + 0.027 s × rows`: the fixed part is the lincheck over the block's `2^28` columns and the witness machinery around it, and one more response costs 27 ms.
So 219 responses cost two full 128-row chunks, and 438 cost three and a 64-row one.
Peak memory is not monotonic in the row count (32 rows peak above 64), which is the allocator and the pooled scratch buffers rather than the protocol; above 128 rows it is set by the largest chunk and grows only slowly.

Verification is about 25 ms per chunk and still flat in the rows a chunk carries, so it amortises the same way it always did — the difference is what a chunk costs.
It used to be about a second, almost all of it the lincheck fold, which Flock's interface makes the verifier compute densely over `2^28` columns.
Evaluating the same matrix claims from the block's structure instead brought that to 62 M field multiplications and 0.8 GB, and it is what `matrix-discharge.md` records.

## What a proof is made of, and what verifying it costs

From `verifier-cost`, built with the `count` feature so Flock's own counters report per phase
(`fixtures/verifier-cost-2026-09-15.summary.log`).

A chunk proof is almost entirely the polynomial-commitment opening, and that is almost entirely
its first level:

| part | 8 responses (m = 31) | 128 responses (m = 35) |
| --- | ---: | ---: |
| whole chunk proof | 510,073 B | 586,065 B |
| Ligerito opening | 494,616 B | 570,448 B |
| — level-0 opened rows (244 queries × 64 words) | 249,856 B | 249,856 B |
| — level-0 Merkle paths | 93,696 B | 124,928 B |
| — deeper levels (rows + paths) | 120,192 B | 162,240 B |
| ring switches | 6,200 B | 6,200 B |
| commitment | 4,137 B | 4,137 B |
| zerocheck + lincheck transcripts | 5,104 B | 5,264 B |
| published words (outside the proof) | 1,920 B | 30,720 B |

The opened rows do not grow with the batch at all — the query schedule is the same — and the
Merkle paths grow only with tree depth. Proof size is therefore set by the PCS profile, not by the
block, and the profile is a runtime choice (`POFSEED_LIGERITO_PROFILE`), measured here on a
128-response chunk:

| profile | rate | proof | prove | verify | peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Fast` (default) | 1/2 | 586,065 B | 6.44 s | 0.03 s | 63.60 GB |
| `Slim` | 1/4 | **378,785 B** | 7.73 s | 0.03 s | 72.74 GB |

A third of the proof for 20% more proving and 14% more memory.
Verification does not notice the profile, because the matrix discharge dominates it and the opening is the small part.
Prover and verifier read the profile independently and a disagreement is refused, not
misverified: it is part of the committed parameters, which the opening compares.

Verification splits the other way round:

| phase | F128 multiplications | inversions | SHA-256 compressions |
| --- | ---: | ---: | ---: |
| opening, 8 responses | 201,565 | 325 | 15,580 |
| opening, 128 responses | 315,510 | 354 | 19,950 |
| core (zerocheck, lincheck, matrix discharge), 8 responses | 62,023,332 | 285 | 0 |
| core, 128 responses | 62,023,356 | 289 | 0 |
| — dense discharge, before 2026-09-15, 8 responses | 713,482,217 | 285 | 0 |
| — dense discharge, before 2026-09-15, 128 responses | 713,482,241 | 289 | 0 |

**The core is 99.5% of the verifier's arithmetic and does not move with the batch**: 24
multiplications separate 8 responses from 128, before the change and after it. It is the matrix
discharge, which depends on the block and not on how many rows carry it, so verification cost is
flat per chunk and amortises: 25 ms buys 8 responses or 128.

That also locates the only obstacle that matters for cheap verification anywhere — on another
machine, in a zkVM, or on chain. The opening is already small: a few hundred thousand field
multiplications and twenty thousand hash compressions. The matrix term is two orders of magnitude
larger — it was four before the structured discharge — and it is an artefact of how this lifter
discharges the matrix claims, not of Flock. What is left of it is the block's 8.7 million explicit
rows; committing to those and proving the evaluation, or deferring them through Flock's
`DeferredMatrixWork` and `matrix_fold`, would bring it to the size of another opening.
`matrix-discharge.md` weighs both.

## Against the SP1 lifter, at 219 responses

| | SP1 lifter (Metal GPU, full path) | Flock lifter (CPU) |
| --- | ---: | ---: |
| prove | 3,613.03 s | 12.33 s |
| peak RSS | 48.39 GB | 73.91 GB |
| proof | 356 B Groth16 + 219 B journal | 1,233,478 B |
| verify | 280,590 gas on L1 (225,975 pairing + 54,615 gate) | 0.06 s native, in 0.82 GB |
| weakest link | BN254 pairing, about 100 bits | Flock `Fast` profile and ZKBoo, 128 classical |

Proving is about **293× faster**, for about half as much memory again (+53%).

### Where the 293× comes from

The SP1 lifter proves a machine; this one proves a relation.

Its guest costs **4.775 × 10⁹ RISC-V instructions** at 219 responses — 21.7 M per response, about
370 per byte of response (`sp1-lifter/knowledge/iteration.md`). The same verification runs natively
in about 2.1 ms per response, so roughly half a second of real work becomes 3,613 s of proving:
**~7,800× slower than native** on its GPU path, ~24,000× on CPU. Three costs multiply — every
word-pool read, refcount and bounds check in `zkboo::verify` is an instruction that must be proven;
each instruction is a proven CPU-state transition over a 31-bit field with memory-consistency and
range arguments around it; and ~280 shards are then recursively compressed, shrunk and wrapped
(~26 s of gnark at the end).

This lifter never executes a machine. Each two-party AND is one committed bit and one R1CS row,
every XOR is free, and the 219-response lift commits about 34 × 10⁹ AND constraints and proves them
in 12.33 s — ~2.8 × 10⁹ AND gates per second. What it pays instead is the compilation: the block is
a hand-written encoding of the verifier, which is why `crates/block/tests/block.rs` exists.
What is traded for it is everything after proving: the SP1 lifter ends in a constant-size proof a contract checks for under 300k gas, and the Flock lifter in a megabyte-scale proof with only a native verifier.
The two also differ in what is trusted: the SP1 guest is the ZKBoo verifier itself, while the Flock block is a compilation of it checked differentially against ZKBoo's replay.
