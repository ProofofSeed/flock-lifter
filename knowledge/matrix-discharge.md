# Discharging the matrix claims

How the verifier checks the lincheck's last equation without building a vector over the block's columns, what that cost before and after, and what is left to do.

## The equation, and why it dominated

Flock's lincheck reduces `z = (A·z) ∘ (B·z)` to one bilinear equation.
Fix a row point and a column point; write `W_row` for the row weights (the "quirky" eq table over the block's `2^k_log` rows, the skipped variables carrying Lagrange weights) and `W_col` for the eq table over the sumcheck's column challenges.
The verifier must evaluate

```
comb_partial[s] = Σ_c W_col(c >> k_skip) · ( α·(Aᵀ·W_row)[c] + (Bᵀ·W_row)[c] )   over columns c ≡ s (mod 2^k_skip)
```

for each of the `2^k_skip = 64` skip slots, and compare `⟨comb_partial, z_partial⟩` against the running sumcheck claim.

Flock's `LincheckCircuit` interface asks for this densely, in three passes over the block width:

1. `build_quirky_eq_table_from_weights` materialises `W_row` at all `2^28` columns;
2. `fold_alpha_batched` returns `α·Aᵀ·W_row + Bᵀ·W_row` as another `2^28`-entry vector;
3. the verifier binds that vector one sumcheck variable at a time, 22 rounds, down to 64 entries.

Measured on a hardened-child chunk (`verifier-cost`, `count` feature), the core cost 713,482,217 field multiplications, of which 168,221,705 were the block's own fold and the remaining ~536.9 M were steps 1 and 3 — Flock's interface rather than this lifter's implementation.
Two vectors of `2^28` F128 elements is 8.6 GB, and it is why verifying a chunk took a second whether it carried 8 responses or 128.

## What replaced it

`verify_lincheck_structured` (`crates/lift/src/chunk_rm.rs`) walks Flock's lincheck transcript byte for byte — same label, same challenges in the same order, same grinding schedule, same shape refusals — but keeps only the running claim through the sumcheck rounds.
Nothing in the replay needs the vector until the last equation, so the vector is never formed; `Program::comb_partial` evaluates those 64 entries directly from the way the block is laid out.

Three facts make that possible:

- **The sub-blocks are aligned.** A `2^16`-bit sub-block boundary splits a column index into a sub-block number and a local offset, and both eq tables factorise across that split — `W(j, p) = W_hi(j) · W_lo(p)`.
- **Every Keccak-f sub-block carries the same local matrix**, and the fold is linear in the row weights. So the local fold (`keccak::fold_shared`, the retired encoder's transpose recurrence) runs **once** instead of 3,988 times, and is re-weighted by `Σ_j W_row_hi(j)·W_col_hi(j)` over the sub-block indices. The constant wire the sub-blocks feed is weighted by `Σ_j W_row_hi(j)` instead, since it lives in the head.
- **The explicit rows cost multiplications only per row and per column slot**, not per nonzero: a row's nonzeros are summed into a 64-slot buffer with field additions (an XOR of two words), and only the slots it touches are multiplied by the row's weight. The A and B sides are accumulated apart so `α` multiplies 64 times at the end rather than once per row, and a row whose B side is the bare constant wire — every row but a replay product — adds its weight to one running scalar.

The two `2^22`-entry eq tables it does build are 134 MB, against 8.6 GB.

## What it costs now

Hardened-child chunk, `verifier-cost` with the `count` feature (`fixtures/verifier-cost-2026-09-15-structured.summary.log`):

| phase | before | after |
| ---------------------------------- | ------------: | -----------: |
| core (zerocheck, lincheck, matrix)  | 713,482,217   | 62,023,332   |
| — of it, the matrix discharge       | 168,221,705 + ~536.9 M in Flock | 62,022,274 |
| opening (ring switch, Ligerito)     | 201,565       | 201,565      |

**11.5× less arithmetic**, and it is still flat in the batch: the block is the same whether the chunk carries 8 responses or 128.

Wall clock and memory, at 219 responses, alternating the two binaries twice each on a quiet machine (`fixtures/matrix-discharge-2026-09-15.summary.log`):

| | dense | structured |
| --- | ---: | ---: |
| verify, whole lift (s) | 1.98, 1.98 | 0.05, 0.05 |
| verify alone, in its own process (s) | 1.997, 1.976 | 0.053, 0.052 |
| verifier peak RSS (GB) | 9.378, 9.369 | 0.822, 0.822 |
| prove (s) | 12.41, 12.60 | 12.64, 12.60 |
| lifted proof (B) | 1,233,478 | 1,233,478 |
| whole-run peak RSS (GB) | 73.910, 73.912 | 73.906, 73.906 |

**Verification is 38× faster and the verifier needs 11.4× less memory.**
Proving and proof size do not move, and the whole-run peak does not either, because the prover's own copy of the dense fold is larger than anything the verifier held.

## That it is the same check

- The proofs are byte-identical, and each verifier accepts the other's: a lift produced by the dense build verifies under the structured one and the other way round.
- `crates/block/tests/block.rs` compares `comb_partial` against the dense route — fold at every column, pin the constant wire, bind 22 rounds — at random points, on the all-gates toy block and (under `--ignored`) on the hardened child at full size. They agree exactly.
- Validated by deletion (`fixtures/deletion-validation-2026-09-15.summary.log`): with the Keccak term dropped from the discharge a good chunk is refused, `ConsistencyFailed { which: "sumcheck-final" }`; with the explicit-row term dropped, likewise; and with the final comparison *also* removed, the chunk with the wrong matrix evaluation verifies. The comparison is what enforces the matrix relation, and the discharge is what it compares.

## What is left

The remaining 62 M multiplications are, roughly: 8.4 M for the two eq tables, ~0.1 M for the Keccak factorisation and the rest for the 8,689,741 explicit rows and their 62,869,716 nonzeros.
The Keccak structure is exhausted; the explicit rows are what is left, and there are two ways further down.

**More structure, no new cryptography.** 6,380,800 of those rows link a Keccak sub-block's input state to wherever it comes from, and across the 1,613 PRG blocks of a slot 1,536 of the 1,600 links per sub-block have *identical* forms — only the counter bits differ.
Collapsing them the way the Keccak fold is collapsed would take roughly another 20 M, at the cost of teaching the block builder to record the grouping.

**Holographic matrices (a real build).** Commit to the block's sparse rows once per statement and prove the evaluation, Spark-style, so the verifier pays an opening instead of the nonzeros.
Flock does not ship a sparse-matrix commitment, and the numbers now argue about its worth: it would replace ~53 M verifier multiplications with a few hundred thousand, but it must commit 62.9 M nonzeros, which is prover work of the same order as the witness commitment the lift already pays.
It is the only route to an on-chain or in-zkVM verifier, and that is the case for it — not the 0.05 s.

**Deferral.** Flock's `LincheckProof::matrix_evals`, `matrix_fold` and `DeferredMatrixWork` exist to let the verifier accept the bilinear forms as claims and fold them into an accumulator for a later proof to discharge.
That is cheaper to reach than a commitment, but it only moves the work unless there is a second proof in the pipeline to put it in.

## The Ethereum-address statement

The earlier reading — that the dense fold vector is what puts the elephant out of reach — was half right, and the half matters.
That statement needs `k_log = 34`, where the dense vector is `2^34` field elements, about 275 GB.
The verifier no longer builds it: its structured discharge would want two `2^28`-entry eq tables, about 8.6 GB, which this machine has.
**The prover still builds it**, because its sumcheck binds the folded vector round by round and genuinely needs every entry; `Program::fold_alpha_batched` is unchanged and still returns `2^k_log` elements.
So the elephant is now blocked by the prover's fold, not the verifier's, and by the compiler's inability to handle inputs allocated after the first AND gate.
