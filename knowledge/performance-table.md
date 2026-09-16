# What everything costs, on this machine

Measured on the machine the SP1 lifter's figures come from: an M4 Max, 16 cores (12 performance, 4 efficiency), 137 GB.
Flock runs on the CPU only, with its NEON kernels and `target-cpu=native`; the SP1 figures it is compared with are on the Metal GPU.
Every row is one process, run one at a time on an otherwise quiet machine, by `lift-bench` under `/usr/bin/time -l`.
Every lift in the table passed verification and the relying-party gate.
The table was first measured on 2026-09-14 (`fixtures/lift-bench-2026-09-14.summary.log`), re-measured on 2026-09-15 with the structured matrix discharge (`fixtures/lift-bench-2026-09-15-structured.summary.log`), and re-measured whole on 2026-09-16 with the regular block layout and the committed-matrix discharge (`fixtures/lift-bench-2026-09-16-committed-matrix.summary.log`).

## The lift

The statement is the SP1 lifter's: BIP-32 hardened child of test vector 1, Keccak-256 suite, one binding.
- **"Prove"** is the whole lift: laying every response into its block, the Flock proofs of every chunk, and the matrix proof.
- **"Verify"** is every chunk's Flock verification with its structured part, the matrix proof, the native Fiat-Shamir gate and the journal.
- **Outside both:**
  - the ZKBoo proof itself (under 0.3 s at 438 responses);
  - building the block from the circuit (0.6 s, once per statement);
  - committing the block's entry list (1.2 s, once per statement).

| responses | chunks | threads | prove (s) | was (s) | verify (s) | lifted proof (B) | was (B)   | peak RSS (GB) |
| --------: | -----: | ------: | --------: | ------: | ---------: | ---------------: | --------: | ------------: |
|         8 |      1 |      16 |      4.15 |    3.38 |       0.01 |          954,094 |   512,341 |         22.40 |
|        16 |      1 |      16 |      4.78 |    3.98 |       0.01 |          971,350 |   529,597 |         33.01 |
|        32 |      1 |      16 |      5.89 |    4.91 |       0.01 |          991,102 |   549,349 |         55.83 |
|        64 |      1 |      16 |      5.37 |    4.44 |       0.01 |        1,030,014 |   588,261 |         42.50 |
|       128 |      1 |      16 |      7.45 |    6.52 |       0.01 |        1,063,686 |   621,933 |         64.78 |
|   **219** |  **2** |  **16** | **13.30** |   12.92 |   **0.02** |    **1,675,231** | 1,233,478 |     **74.77** |
|       438 |      4 |      16 |     23.99 |   22.91 |       0.02 |        2,892,929 | 2,451,176 |         79.70 |
|        64 |      1 |      12 |      5.45 |    4.51 |       0.01 |        1,030,014 |   588,261 |         42.02 |
|       128 |      1 |      12 |      8.23 |    7.34 |       0.01 |        1,063,686 |   621,933 |         64.35 |
|       219 |      2 |      12 |     15.23 |   14.48 |       0.02 |        1,675,231 | 1,233,478 |         74.38 |
|       438 |      4 |      12 |     27.85 |   25.52 |       0.05 |        2,892,929 | 2,451,176 |         79.24 |

"Was" is the 2026-09-15 figure, with the compact layout and the verifier walking the explicit rows.
- **Proving** costs 0.4–2.3 s more. Most of it is the matrix proof, which is about a second whatever the lift's size, since one proof covers every chunk.
- **The proof** grows by a flat 441,753 bytes, the matrix proof.
- **Peak memory** grows by about 1 GB.
- **Verification** drops to 10–50 ms. It no longer evaluates any explicit row: it pairs each chunk's Keccak sub-blocks in rotation-invariant form and checks one matrix proof (`committed-matrix.md`).
- **One outlier.** The 438-response row at 12 threads is the first of two agreeing repeats; a first run at 32.36 s was an outlier and is kept in the fixture.

A lift is chunks of at most 128 responses, and each chunk proves a power-of-two number of rows, the last live block repeated as padding.
Within one chunk, prove time is about `3.0 s + 0.027 s × rows`: the fixed part is the lincheck over the block's `2^28` columns and the witness machinery around it, and one more response costs 27 ms.
So 219 responses cost two full 128-row chunks, and 438 cost three and a 64-row one.
Peak memory is not monotonic in the row count (32 rows peak above 64), which is the allocator and the pooled scratch buffers rather than the protocol; above 128 rows it is set by the largest chunk and grows only slowly.

Verification is a few milliseconds per chunk plus one matrix proof, flat in the rows a chunk carries.
It was once about a second, almost all of it the lincheck fold, which Flock's interface makes the verifier compute densely over `2^28` columns.
Evaluating the same matrix claims from the block's structure brought that to 62 M field multiplications (`matrix-discharge.md`), and committing the explicit rows removed most of what was left (`committed-matrix.md`).

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
rows. Removing them from the verifier entirely, through Flock's claim accumulation, was costed on
2026-09-15 and declined: it would cost the prover about 2.5 s and 21 GB at 219 responses to save
the verifier 25 ms. `matrix-discharge.md` records the costing and why it becomes the right build
the moment chunk verification is arithmetised.

## Against the SP1 lifter, at 219 responses

| | SP1 lifter (Metal GPU, full path) | Flock lifter (CPU) |
| --- | ---: | ---: |
| prove | 3,613.03 s | 13.30 s |
| peak RSS | 48.39 GB | 74.77 GB |
| proof | 356 B Groth16 + 219 B journal | 1,675,231 B |
| verify | 280,590 gas on L1 (225,975 pairing + 54,615 gate) | 0.02 s native; 1.27 B gas in EVM contracts |
| weakest link | BN254 pairing, about 100 bits | Flock `Fast` profile and ZKBoo, 128 classical |

Proving is about **272× faster** (it was 293× before the matrix proof), for about half as much memory again (+55%).

### Where the gap comes from

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
in about 13 s — ~2.6 × 10⁹ AND gates per second. What it pays instead is the compilation: the block is
a hand-written encoding of the verifier, which is why `crates/block/tests/block.rs` exists.
What is traded for it is everything after proving: the SP1 lifter ends in a constant-size proof a contract checks for under 300k gas, and the Flock lifter in a megabyte-scale proof whose EVM verification costs over half a million times as much.
The two also differ in what is trusted: the SP1 guest is the ZKBoo verifier itself, while the Flock block is a compilation of it checked differentially against ZKBoo's replay.

## On chain

From `evm-bench 219` on 2026-09-16, in an in-process EVM under Osaka rules with the gas cap and the size limits lifted (`fixtures/evm-bench-2026-09-16-*.summary.log`).
Gas includes calldata at standard pricing.
The transaction count is a lower bound, because the verification is not yet split into transactions; `evm-verifier.md` records what is missing and why.

| contracts                     | lift contract (M gas) | matrix discharge (M gas) | in all (M gas) | transactions at 2^24, at least |
| ----------------------------- | --------------------: | -----------------------: | -------------: | -----------------------------: |
| first working version         |              1,138.56 |                  670,934 |        672,073 |                         40,059 |
| optimised, `Fast` profile     |                830.28 |                  157,512 |        158,342 |                          9,438 |
| optimised, `Slim` profile     |                680.28 |                  157,512 |        158,192 |                          9,429 |
| regular layout, committed matrix, `Fast` |     830.43 |                   435.47 |       1,265.90 |                             76 |

The row-walking discharge did not depend on the profile, and was 99% of the total; the committed discharge's figures are `fixtures/evm-bench-2026-09-16-committed-final.summary.log`, and `committed-matrix.md` breaks them down.
