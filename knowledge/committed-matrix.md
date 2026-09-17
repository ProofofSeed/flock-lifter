# The regular layout and the committed matrix

Status: built and measured, 2026-09-16.
A lift now discharges its matrix claims through a proof against a list of entries committed once per statement, instead of making the verifier walk the block's explicit rows.
What made that affordable is a regular layout of the block, in which the rows of one gate differ only by a cyclic shift.
On Ethereum, verifying the 219-response hardened-child lift went from 158.3 billion gas to 1.27 billion, at least 76 transactions at the 2^24-gas cap. Evaluating Ligerito's final-level residuals in assembly (below) then took it to **758 million**, at least 46 transactions.
Natively, verification went from 0.06 s to 0.02 s, for 0.4 s more proving at 219 responses, 441,753 more proof bytes and a 1.2 s commitment once per statement.

## Why the rows had to be regular

A matrix claim's explicit-row part is a sum over nonzeros.
Each nonzero contributes a side factor (α for the A side, 1 for B), a row weight `skip[t]·eq(x, W)` for its row column `W·64 + t`, and a column weight `z[t']·eq(r, W')` for its operand column `W'·64 + t'`.
Rows of one output word whose operands keep a fixed word and a fixed cyclic bit offset form a *class*. A class sums in closed form over any contiguous run of its row bits, through prefix sums of `skip[t]·z[(t + u) mod 64]`.

The compact layout the lifter used defeated this. It allocates columns in evaluation order, so one 64-column word holds bits of different gates. Three things also vary from bit to bit:
- products are skipped wherever the chain code or a round constant makes an operand constant;
- a form is materialised only once it exceeds 32 terms;
- an operand of constant 1 is folded away.

`verifier-routes.md` measured the result: 2,691,922 of 2,718,991 row records sat alone in their class.

**The regular layout** (`replay::compile_regular`, now `Program::new`; the old layout is `Program::compact`) lays out every gate the same way at every bit:
- every product is committed, with a constant operand kept as a masked reference to the constant column;
- AND and carry outputs are always materialised;
- a linear gate materialises at all its bits or at none;
- every column kind of every gate limb gets its own 64-bit word, with bit `b` at column `b`.

| hardened-child block | compact       | regular       |
| -------------------- | ------------: | ------------: |
| `k_log`              |            28 |            28 |
| replay rows          |     1,894,121 |     2,685,558 |
| explicit rows        |     8,689,741 |     9,481,178 |
| explicit nonzeros    |    62,869,716 |    55,601,381 |
| entries (below)      |    90,009,079 | **3,059,456** |

- **Correctness.** The regular block passes the block's full-size differential tests (`crates/block/tests/block.rs`): agreement with ZKBoo's native replay under every challenge, and the structured discharge against the dense fold.
- **Prover cost.** Proving a 128-response chunk took 6.47 s and 6.44 s against 6.58 s and 6.54 s for the compact layout, alternated on one machine, with the same proof size and 0.07 GB more peak memory (`fixtures/uniform-layout-2026-09-16.summary.log`).

## The entry list

`committed::entries` (in `crates/block`) turns the explicit rows into a sorted list of entries, one or two per operand per run of a class. Entries occurring an even number of times cancel and are dropped.

Each entry packs into 59 bits: a side bit, a 22-bit row word, a 22-bit column word, and a 14-bit prefix-table address `u·128 + j`. Here `u < 64` is a cyclic offset, or `64 + b` for an operand whose column keeps bit `b`, and `j ≤ 64` is a run end.

For a claim with A-side challenge α, row skip weights `skip`, collapsed witness `z`, and points `x` and `r`, an entry reads eight tables:
- `[α, 1]`;
- the `eq` tables of `x` in 8-, 8- and 6-coordinate pieces;
- the same three for `r`;
- the prefix table `P[u][j] = Σ_{t<j} skip[t]·Z_u[t]`.

It contributes their product. `crates/block/tests/committed.rs` checks that the list's weighted sum equals the explicit rows' part of the discharge at full size, for both layouts. For the compact layout the list exists but, at 90 M entries, is not worth committing.

## The proof

`crates/lift/src/matrix.rs`. The list is padded to `2^22` entries with entries that read zero, and its packed bits, `2^28` of them, are committed with Flock's PCS once per statement (`MatrixKey`, `LiftKey`). A verifier pins the commitment (`MatrixCommitment`), which anyone can recompute from the statement. Per lift, over the claims of all its chunks, batched by `μ`, the proof runs:

1. **Main sumcheck.** A degree-8 sumcheck of `Σ_k Σ_c μ^c·Π_l T_{c,l}[a_l(k)]` over the entry index reduces the sum to a point `ρ`.
2. **Counts.** The prover sends, for each lookup, the counts `ĉ_l[a] = Σ_k eq(ρ, k)·[a_l(k) = a]`, 9,474 values in all. The verifier forms every `Σ_a T_{c,l}[a]·ĉ_l[a]` itself and checks the main sumcheck's final claim.
3. **Count check.** Random address points `r_l` and a batching `γ` reduce the counts' correctness to `Σ_k eq(ρ, k)·Σ_l γ^l·Π_i (1 + r_{l,i} + A_{l,i}(k))`. A degree-15 sumcheck over the entries' address bits `A` proves it, ending at a point `σ`.
4. **Opening.** The prover sends the 59 address bits' extensions at `σ`. One evaluation claim on the committed list, with the bit positions as Flock's skipped variables at a random `ζ`, is opened with Ligerito.

The chunk verifier no longer evaluates the explicit rows. `verify_chunk_deferred` computes the claim's structured part (Keccak sub-blocks and constant-wire pin) and hands `running − structured` to the matrix proof. The lifted proof carries one `MatrixProof`, whose transcript domain is the lift's statement digest.

**Soundness accounting.** This is our own accounting, not audited. Each challenge is ground so that its round-by-round error is at most `2^-128`:

| challenge                         | error before grinding           | grinding bits |
| --------------------------------- | ------------------------------- | ------------: |
| main sumcheck round, degree 8     | `8/2^128`                       |             3 |
| count sumcheck round, degree 15   | `15/2^128`                      |             4 |
| count points and their batching   | `(14 + 7)/2^128`                |             5 |
| skip point of the opening         | `63/2^128`                      |             6 |
| claim batching `μ`                | `(C − 1)/2^128` for `C` claims  |             2 |

- **Claim batching.** Two grinding bits cover lifts of up to four chunks (438 responses); a larger lift needs more.
- **The opening** is Flock's Ligerito under the registered `m = 28` configuration of the same profile as the chunks.
- **The committed list** is trusted to be the statement's own, because the verifier pins it and anyone can rebuild it. No proof of its well-formedness is made, and none is needed for that reason.

**Validation** (`fixtures/deletion-validation-2026-09-16-committed-matrix.summary.log`):
- **Forgeries.** A forging prover (`prove_forged`, feature `forgery`) makes proofs of a wrong value that pass the main sumcheck by adjusting a count, and proofs that also pass the count sumcheck by adjusting an address bit. Each is refused by exactly the check it targets.
- **Deletion.** With that check deleted, each forgery is accepted.
- **Acceptance.** The run gained three cases, all refused: a tampered matrix proof, a missing one, and another lift's (`fixtures/acceptance-both-2026-09-16-committed-matrix.summary.log`).

**Native cost at 219 responses.**
- **Proving.** The key takes 1.2 s once per statement. Proving takes 13.30 s against 12.92 s (16 threads), with 74.77 GB peak against 73.91, and the proof grows by 441,753 bytes to 1,675,231 (`fixtures/lift-bench-2026-09-16-committed-matrix.summary.log`, quiet machine; across the table's sizes the matrix proof adds 0.4–2.3 s).
- **Verifying.** Verification takes 0.02 s against 0.06 s.

## The Keccak sub-blocks in rotation-invariant form

The structured part is evaluated differently too, natively and on chain (`keccak::fold_shared_paired`, `Program::structured_value`, `verifier/src/Structured.sol`).

- **Circulant fold.** Every map in the shared Keccak-f fold commutes with rotating all lanes together. So under row weights `skip ⊗ row` the fold is, lane by lane, `skip` convolved with a kernel, and the kernel is the fold of the row weights alone, placed at bit 0 of each lane.
- **Pairing.** Pairing with the columns becomes, per lane, the kernel against the 64 values `Σ_u skip[u]·z[(u + d) mod 64]`.
- **Round constants.** They enter the constant-wire part exactly where their round's χ outputs enter the columns, so that part is the round constants' bits paired with the same kernels.
- **Sub-block sums.** The sums over the sub-block range have a closed form in the high coordinates.
- **Checks.** `crates/block` tests the kernel form against the dense fold and the paired value against the old per-slot discharge, the latter at full size.

On chain this replaced the 1,037 M gas `keccakPart` call with about 70 M per claim inside the matrix contract. What remains is dominated by about 40,000 products of kernel coefficients with the 64 pairing values per claim. Each is an 8-bit table multiplication of about 1,000 gas, which is roughly the opcode count such a multiplication needs.

## What it costs on chain

`evm-bench 219` (`fixtures/evm-bench-2026-09-16-committed-final.summary.log`), gas in millions:

| part                                |      before |    committed | residuals in assembly |
| ----------------------------------- | ----------: | -----------: | --------------------: |
| lift contract (two chunks, gate)    |      830.28 |       830.43 |                432.16 |
| structured parts (Keccak, pin)      |    1,037.24 |       139.68 |                139.68 |
| explicit rows, with the final check |     153,362 |            — |                     — |
| matrix proof: sumchecks and counts  |           — |        70.47 |                 70.47 |
| matrix proof: opening               |           — |       219.33 |                110.00 |
| calldata of the discharge           |       3,112 |         5.99 |                  5.99 |
| **verification in all**             | **158,342** | **1,265.90** |            **758.30** |
| transactions at 2^24, at least      |       9,438 |           76 |                    46 |

- **"Before"** is `evm-bench-2026-09-16-optimised.summary.log`: the compact layout with the row-stream discharge.
- **"Residuals in assembly"** is `evm-bench-2026-09-17-residuals-fast.summary.log`, described in the next section.
- **`Slim` profile.** Under `POFSEED_LIGERITO_PROFILE=slim` the committed column costs 680.22 M (lift) + 379.96 M (matrix) = 1,060.18 M, at least 64 transactions (`fixtures/evm-bench-2026-09-17-committed-slim.summary.log`), and the last column 343.40 M + 304.43 M = **647.83 M**, at least 39 (`fixtures/evm-bench-2026-09-17-residuals-slim.summary.log`). The saving is in the openings' level-0 rows and consistency residuals; the ring-switch residuals and the structured parts do not depend on the profile.
- **Deployment.** The matrix contract (`FlockMatrix`) cost 20.3 M gas to deploy, and its runtime was 94,197 bytes, over EIP-170's limit like the lift contract's 94,320. With the schedules generated as a byte table both are now about 53 KB, still over; `staged-verification.md` describes the contracts that are deployed instead.

## Ligerito's final-level residuals in assembly

In the committed column, Ligerito's final-level verification dominated. It is shared code, paid once per opening, and there are three openings: one per chunk and one for the matrix. Their ring-switch and consistency residuals cost 187 + 126, 189 + 126 and 66 + 120 M: 814 M of the 1,266 M. `verifier/src/Residual.sol` now evaluates both, each already paired with the final check's weights `μ`, so the residual vector is never formed. The file is generated by `verifier/tools/residual.py`, which unrolls its table builds and lookups.

**The ring-switch residual.** It evaluates, per claim, a product of one factor `1 ⊗ w_i + q_i ⊗ 1` per prefix coordinate in `GF(2^256) ⊗ GF(2^128)`, then contracts it at every binary suffix `y`.
- **Scalar factors.** The algebra is commutative. So a factor whose right-hand coordinate is 0 or 1 is a left scalar and is multiplied out, costing one product instead of a table step. The published-word claim has 17 such coordinates out of 24.
- **Rank expansion.** The first five generic factors are expanded as a sum of 32 pure tensors, turned into columns through one small table.
- **Steps.** The tensor is held as 128 columns in `GF(2^256)`. The right-hand part of a step mixes the columns through one 8-bit combination table. The left-hand part multiplies each column by the fixed `q_i`, through three Horner tables with 8-bit windows, about 700 gas per product. A step costs about 0.65 M, against 1.9 M before.
- **Points.** Each suffix point takes 128 lookups of `L(x^b·s_y)`, a transposition of those values by byte-spread tables, and 128 lookups in the columns' table, which is built once per claim.
- **Finishing map.** Precomputing it once per claim, as a table of its values on a basis, was costed and rejected. That is 128 evaluations at about the cost of a point, against 16 or 32 points.

**The consistency residual.** Per level, it is the sum over the queries of a weight, a prefix product `Π_{k<f} (1 + r_k·(1 + w_k(q)))` and a suffix form in `μ`.
- **Prefix factors.** `w_k(q)` depends only on the bits of `q` from `k` up, because the subspace table is triangular with a unit diagonal. For levels with at least 32 queries, each factor is therefore read from an 8-bit affine table over `q >> k`, built once per level.
- **Suffix form.** It depends only on `q >> f`. When those bits are few, the queries are grouped by them, and the form is folded for every value of them at once, one variable at a time. This is `ext·2^bits` products instead of one fold per query.
- **What remains.** About `f` generic `GF(2^256)` products per query. At about 5.8k gas each (three 4-bit-window products), they are most of what is left.

**Windows.** Combination tables use 8-bit windows with unrolled builds, about 122k gas each against 326k looped, and 16-fetch lookups using `BYTE`. With lookups in the hundreds per table, 5- and 6-bit windows came out no cheaper. Generic products keep 4-bit windows, scanned a byte at a time.

**Checks.**
- `crates/evm/tests/residual.rs` compares both routines against the implementations they replaced, which are kept under `verifier/src/probes/`. It uses random inputs covering every path: binary coordinates, the tabled, plain, bucketed and tree paths, and one to three claims.
- The mirror, contract and matrix tests pass unchanged, tampering refusals included.

**Result** (`fixtures/evm-bench-2026-09-17-residuals-fast.summary.log`):

| opening | ring switch, before (M gas) | ring switch, now (M gas) | consistency, before (M gas) | consistency, now (M gas) |
| ------- | --------------------------: | -----------------------: | --------------------------: | -----------------------: |
| chunk 1 |                      186.76 |                    51.17 |                      125.63 |                    64.50 |
| chunk 2 |                      189.04 |                    51.65 |                      126.27 |                    64.58 |
| matrix  |                       65.55 |                    23.73 |                      119.68 |                    52.30 |

The six residuals went from 812.9 M to 307.9 M, and verification from 1,265.90 M to **758.30 M**. The runtime code grew by 8,562 bytes.

**What dominates now.**
- **Matrix contract.** The structured parts are 139.7 M. The main sumcheck and count claim are 68.5 M, still made of Solidity multiplications.
- **Lift contract.** Per chunk, the residuals are about 116 M, the level-0 opening 47 M, and the published-word claim 14 M.

## What is still open

- **Transaction splitting and code size.** Done since: `staged-verification.md` runs the same checks in 106 transactions under the cap, from contracts under EIP-170's limit, with the matrix session bound to the claims a lift session recorded. The single calls here remain the reference. `optimistic-verification.md` describes the alternative built beside this route, which disputes these two calls instead of running them.
- **Larger lifts.** The claim-batching grinding covers at most four chunks.
