# Plan: discharging the matrix claims without touching every column

Approved by Stefano on 2026-09-15, off the measurement in `performance-table.md`: verifying a chunk
costs 713,482,217 field multiplications in the core against 201,565 in the opening, and the core's
figure does not move with the batch (24 multiplications separate 8 responses from 128).

## What the 713 million are

The lincheck's consistency check is a bilinear form `⟨W_row, M · W_col⟩` over the block's base
matrices, and Flock's `LincheckCircuit` interface asks for it densely:

- `build_quirky_eq_table_from_weights` materialises the row weight over all `2^28` columns — one
  multiplication each, ~268 M;
- the final inner product runs over the same `2^28`, ~268 M;
- `Program::fold_alpha_batched` returns a `2^28`-entry vector (4.3 GB), and computing it costs
  ~180 M multiplications, most of them the Keccak sub-blocks' transpose recurrence.

The split above is arithmetic, not measurement: the three terms sum to ~716 M against the measured
713 M. **Confirm it with a counter around the fold before building on it** — if the fold is a
larger share than this says, the tiers below reorder.

The consequence that matters: **making the fold structured is not enough.** Two thirds of the cost
is the interface, not the implementation. Any fix has to replace the discharge itself.

## Tiers

**T1 — structured bilinear discharge.** Verify the lincheck's final equation ourselves, evaluating
`⟨W_row, M · W_col⟩` from the block's structure instead of materialising anything: the Keccak
sub-blocks are aligned, so their contribution factorises into one local evaluation times a sum of
`eq` products over sub-block indices, and only the explicit rows are paid per nonzero (~63 M).
Expect ~130 M multiplications and no `2^28` allocation. This replays the same maths Flock's own
deferred path uses on the union side (`MatrixAssertion::claims`, `matrix_fold::bilinear`), so the
shape is already in the codebase; what it needs here is our own copy of the row-major lincheck's
final check, since `verify_with_grinding` is monolithic.

Side effect worth having: the `2^28`-entry fold vector is what puts the Ethereum-address statement
out of reach (`k_log = 34` would need ~275 GB). T1 removes that vector, so the elephant becomes a
memory question about the prover rather than an impossible one about the verifier.

**T2 — holographic matrices.** Commit to the base matrices once per statement and open the
evaluation, Spark-style. This is what takes the verifier from `O(nonzeros)` to the size of another
opening (a few hundred thousand multiplications), and it is the only tier that makes a cheap
on-chain or in-zkVM verifier possible. Flock does not ship a sparse-matrix commitment, so this is
a real build.

**T3 — deferred into a second proof.** Flock's `DeferredMatrixWork` and `matrix_fold` exist to fold
matrix claims into an accumulator that a later proof discharges. Cheaper to reach than T2 if a
second Flock proof is acceptable in the pipeline, and it composes with the recursion tower.

## Order and acceptance

Start at T1, measure, then decide between T2 and T3 with that number in hand.

T1 is done when: the counting probe shows the core's multiplications down from 713 M to the
predicted order and the dense allocation gone; `acceptance both` still passes, reject matrix
included; the lift's verification time is re-measured in `performance-table.md`; and a deliberately
wrong matrix evaluation is refused, validated by deletion as the other checks were.
