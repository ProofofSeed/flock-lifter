# What everything costs, on this machine

Measured on 2026-09-14 on the machine the SP1 lifter's figures come from: an M4 Max, 16 cores (12 performance, 4 efficiency), 137 GB.
Flock runs on the CPU only, with its NEON kernels and `target-cpu=native`; the SP1 figures it is compared with are on the Metal GPU.
Every row is one process, run one at a time on an otherwise quiet machine, by `lift-bench` under `/usr/bin/time -l`; the log is `fixtures/lift-bench-2026-09-14.summary.log`.
Every lift in the table passed verification and the relying-party gate.

## The lift

The statement is the SP1 lifter's: BIP-32 hardened child of test vector 1, Keccak-256 suite, one binding.
"Prove" is the whole lift: laying every response into its block, and the Flock proofs of every chunk.
"Verify" is every chunk's Flock verification, the native Fiat-Shamir gate and the journal.
The ZKBoo proof itself (under 0.2 s at 438 responses) and building the block from the circuit (0.62 s, once per statement) are outside both.

| responses | chunks | threads | prove (s) | verify (s) | lifted proof (B) | peak RSS (GB) |
| --------: | -----: | ------: | --------: | ---------: | ---------------: | ------------: |
|         8 |      1 |      16 |      3.19 |       1.01 |          512,341 |         21.49 |
|        16 |      1 |      16 |      3.80 |       1.02 |          529,597 |         32.11 |
|        32 |      1 |      16 |      4.82 |       1.01 |          549,349 |         54.79 |
|        64 |      1 |      16 |      4.42 |       1.00 |          588,261 |         41.62 |
|       128 |      1 |      16 |      6.38 |       0.98 |          621,933 |         63.61 |
|   **219** |  **2** |  **16** | **12.33** |   **1.97** |    **1,233,478** |     **73.91** |
|       438 |      4 |      16 |     22.71 |       3.95 |        2,451,176 |         78.82 |
|        64 |      1 |      12 |      4.53 |       1.09 |          588,261 |         41.20 |
|       128 |      1 |      12 |      7.30 |       1.03 |          621,933 |         63.20 |
|       219 |      2 |      12 |     14.24 |       2.05 |        1,233,478 |         73.60 |
|       438 |      4 |      12 |     25.42 |       4.18 |        2,451,176 |         78.51 |

A lift is chunks of at most 128 responses, and each chunk proves a power-of-two number of rows, the last live block repeated as padding.
Within one chunk, prove time is about `3.0 s + 0.027 s × rows`: the fixed part is the lincheck over the block's `2^28` columns and the witness machinery around it, and one more response costs 27 ms.
So 219 responses cost two full 128-row chunks, and 438 cost three and a 64-row one.
Peak memory is not monotonic in the row count (32 rows peak above 64), which is the allocator and the pooled scratch buffers rather than the protocol; above 128 rows it is set by the largest chunk and grows only slowly.

Verification is about one second per chunk, almost all of it the lincheck fold, which Flock's interface makes the verifier compute densely over `2^28` columns.
The block's aligned sub-blocks would let the verifier evaluate the same matrix claims from one sub-block fold and the sparse rows instead, as `design.md` describes; that discharge is not built.

## Against the SP1 lifter, at 219 responses

| | SP1 lifter (Metal GPU, full path) | Flock lifter (CPU) |
| --- | ---: | ---: |
| prove | 3,613.03 s | 12.33 s |
| peak RSS | 48.39 GB | 73.91 GB |
| proof | 356 B Groth16 + 219 B journal | 1,233,478 B |
| verify | 280,590 gas on L1 (225,975 pairing + 54,615 gate) | 1.97 s native |
| weakest link | BN254 pairing, about 100 bits | Flock `Fast` profile and ZKBoo, 128 classical |

Proving is about **293× faster**, for about half as much memory again (+53%).
What is traded for it is everything after proving: the SP1 lifter ends in a constant-size proof a contract checks for under 300k gas, and the Flock lifter in a megabyte-scale proof with only a native verifier.
The two also differ in what is trusted: the SP1 guest is the ZKBoo verifier itself, while the Flock block is a compilation of it checked differentially against ZKBoo's replay.
