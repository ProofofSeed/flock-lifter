# Routes to a deployable verifier: initial investigation

Status: exploratory, 2026-09-16.
Afterwards the same day, routes 1 and 2 were built together, which took verification to 1.27 billion gas (`committed-matrix.md`). Route 3 is not pursued, because wrapping in a pairing SNARK gives up what the Flock lifter is for. Route 4 is being prototyped on its own branch.
`evm-verifier.md` measured a direct EVM verifier for the 219-response lift at 158.3 billion gas and named four routes that could change that by orders of magnitude.
This note investigates each one far enough to cost it: one route is built and measured, one uses measured primitive costs, and two are estimated from what is already measured.
Every figure is marked as measured, modelled or estimated.

## Summary

| route                              | on-chain cost, 219 responses        | prover cost           | status                                   |
| ---------------------------------- | ----------------------------------- | --------------------- | ---------------------------------------- |
| today's contracts                  | 158 B gas, ≥ 9,438 tx (measured)    | —                     | built                                    |
| uniform block layout               | ~15–18 B gas, ~1,000 tx (modelled)  | none measurable       | block built and tested; contract not built |
| — with claim accumulation          | ~9 B gas (modelled)                 | ~+2.5 s, ~+21 GB      | costed 2026-09-15                        |
| committed matrix                   | ~2–3 B gas, ~150 tx (estimated)     | a few s per chunk     | new cryptography, not started            |
| wrapping in SP1                    | ~280 k gas                          | see below             | beats SP1 alone only after the committed matrix |
| optimistic verification            | ~10^5 gas plus data, if unchallenged | none                  | a different trust model                  |

No route makes a *direct* Flock verifier cheap on L1: even both structural routes together leave billions of gas.
The two routes that reach ordinary transaction costs replace verification with something else: a pairing SNARK (wrapping) or an economic game (optimistic verification).

## Route 2: a uniform block layout

### What makes the rows irregular

A contract could sum rows in closed form if their weights factorised.
The discharge weight of an explicit row is already a product: a per-word row weight times a per-bit weight `skip[bit]`, and for each operand a per-word column weight times `zp[bit]`.
So a group of rows in one output word whose operands keep a fixed word and a fixed cyclic bit offset — a *class* — sums to one product per distinct offset.
`run-classes` groups the discharge stream this way: of 2,718,991 row records, **2,691,922 are alone in their class**.

Printing the rows shows why (`CLASS_WORD` and `PROBE_GATE` dump them).
The compiler allocates columns in evaluation order, so one "word" of 64 columns holds bits of different gates.
Each AND bit makes four product columns and up to two materialised ones.
Three things then vary from bit to bit:
- products are skipped when an operand is a constant, and the chain code, the SHA-512 initial values and the round constants are compiled in as constants;
- a form is materialised only when it exceeds 32 terms;
- products with a constant 1 operand are replaced by the other operand (the `is_one` shortcut).

### A uniform compile

`replay::compile_uniform` (since renamed `compile_regular` and made the default, `Program::new`) lays out every gate the same way at every bit:
- no product is skipped: a constant operand becomes a masked reference to the constant column;
- the outputs of AND and carry gates are always materialised;
- linear gates materialise at all their bits or at none.

`Program::uniform` (now `Program::new`) builds a block from it with no other change, because the witness generator, the prover and the structured discharge are generic in the rows.

Measured (`fixtures/uniform-layout-2026-09-16.summary.log`):

| block    | replay rows | products  | materialised | explicit rows | prove, 128 responses (s) | peak RSS (GB) | proof (B) |
| -------- | ----------: | --------: | -----------: | ------------: | -----------------------: | ------------: | --------: |
| compact  |   1,894,121 | 1,579,812 |      314,309 |     8,689,741 |               6.58, 6.54 |         63.62 |   586,065 |
| uniform  |   2,685,558 | 1,638,308 |    1,047,250 |     9,481,178 |               6.47, 6.44 |         63.69 |   586,065 |

- Both blocks stay at `k_log = 28`.
- The uniform block passes the block's differential tests at full size: agreement with ZKBoo's native replay under all three challenges, and the structured discharge against the dense fold. It also passes both toy tests, and a chunk proof over it verifies and refuses a tampered published word.
- **Proving is not slower** (the two layouts alternated twice, 128 responses). The head is about 1% of the block, and the extra rows cost the prover nothing measurable.

### What it would cost a contract

`layout-probe` groups the rows into classes on a virtual layout, one 64-bit word per gate, column kind and limb. It then costs each class at 1,800 gas per field multiplication (one per distinct bit offset per side, plus the row weight), 150 per table lookup and 2,000 per class.
The same model gives 80.7 B gas per claim for today's replay rows, against about 70 B measured, so it is about 15% pessimistic.

| replay rows                                     | classes   | operands   | multiplications | modelled gas per claim |
| ----------------------------------------------- | --------: | ---------: | --------------: | ---------------------: |
| as compiled                                     | 1,893,654 | 48,824,828 |      32,937,313 |                 80.7 B |
| as compiled, remapped bit-aligned               | 1,292,205 | 39,260,045 |       9,719,849 |                 30.2 B |
| **uniform, bit-aligned**                        |   227,123 |  5,660,561 |       2,403,675 |              **7.2 B** |
| uniform, the other stream rows (preimages etc.) |    26,059 |     27,260 |          52,581 |                 0.17 B |

Remapping the current rows is not enough, because the per-bit variation is in the rows themselves; the uniform compile is what collapses them.
Of the uniform classes, 3,652 cover a whole word and 154,590 a contiguous range of bits: carry chains stop at bit 63, and tape offsets cross word boundaries mid-gate.
A prefix table handles a contiguous range with two lookups; the remaining 68,881 classes need 8-bit mask tables.

**Estimate for the whole verification:** 7.3 B per claim, so about 14.6 B for two claims (about 12.6 B after the model's pessimism). Adding the Keccak part (1.04 B measured), the lift contract (0.83 B measured) and the table setup gives **about 15–18 B gas, roughly 1,000 transactions: a tenth of today, still far from viable.**
Flock's claim accumulation (`matrix-discharge.md`) would fold the two claims into one and halve the discharge, to about 9 B in all, for the prover cost measured on 2026-09-15.

The remaining cost is about ten distinct bit offsets per class, each a full field multiplication. SHA-512's rotations and the tape offsets are what make them distinct. Whether 8-bit tables per (range, offset) pair would pay for their memory has not been counted.

## Route 1: a committed matrix

The matrix is fixed per statement, so the literal holographic construction is available: commit its sparse description once at deployment, and have each proof show that its matrix claims are evaluations of the committed matrix. This is Spark-style offline memory checking.
The 2026-09-15 costing rejected this for the *native* verifier. On chain the balance is different.

What the discharge's existing structure does for it:
- **The memories are tiny.** A row's weight is `skip[bit] · rowW[word]`, and an operand's is `zp[bit] · colW[word]`. The memory-checking tables are therefore the 64 bit weights and the head's word weights (about 36–42 k entries), not `2^28` entries. Their multilinear extensions are `eq` restrictions the verifier evaluates in closed form.
- **Per proof, the prover commits the looked-up values.** There is one entry per nonzero: about 49 M F128 values for today's replay rows, about 2^33.6 bits, some 37% of the witness polynomial's `2^35`.
- **On the uniform layout, the committed description could be the class list instead:** 5.7 M operands, each looked up as a row weight, a column weight and a range-offset factor. That is nine times less per-proof commitment.
- **The Keccak sub-blocks and the closed-form families stay as they are.** They already cost about 1 B gas together.

Estimated on-chain cost per chunk:
- one sumcheck over about 23–26 variables;
- grand-product arguments over the lookups, a few tens of millions of gas at the measured field-operation prices;
- above all, a **second Ligerito opening** for the per-proof commitment, plus an opening of the preprocessed one. By analogy with the measured opening (300–400 M per chunk including its residuals), that is several hundred million gas per chunk.

**Total: about 2–3 B gas, of the order of 150 transactions.**
The prover pays one more commitment and the grand products per chunk, probably a few seconds. This is not measured.

What it needs:
- **new cryptography over GF(2^128).** Memory-checking timestamps need a multiplicative counter, since characteristic 2 has no useful `+1`. Flock ships nothing of this: its `matrix_fold` module says deliberately that no sparse-matrix commitment is needed.
- **a soundness argument** for the combination.
- **several weeks of work.** It is the only route that removes the discharge from verification rather than moving it.

## Route 3: wrapping in a succinct proof

Prove the Flock verifier inside SP1 and verify SP1's Groth16 wrap on L1 for about 280 k gas, as the SP1 lifter does. The question is whether proving the Flock verifier costs SP1 less than proving the ZKBoo verifier directly.

Measured SP1 6.4.0 costs per operation, executed and not proved (`fixtures/sp1-op-costs-2026-09-16.summary.log`). A precompile call counts one instruction; its real proving cost is not in these counts.

| operation                                           | RISC-V instructions |
| --------------------------------------------------- | ------------------: |
| GF(2^128) multiplication, Flock's portable path     |               2,264 |
| GF(2^128) squaring, Flock's portable path           |               1,145 |
| 4-bit windowed multiplication                       |                 935 |
| 8-bit table multiplication, per lookup (build 5,675) |                349 |
| SHA-256 compression, SP1-patched (plus a precompile) |                510 |
| SHA-256 compression, unpatched                      |               4,048 |
| Keccak-256 of 64 bytes, SP1-patched (plus a precompile) |             953 |

- **Can SP1 run Flock's verifier?** `flock-core` compiles for SP1's target with rayon, blake3 and bincode. Its verifier entry points run inside a dedicated one-thread pool, which SP1 cannot create, so they would panic. The fix looks shallow; the pool exists for stack depth, which has not been checked against the zkVM. No full verification was executed.

The native verifier does 62.0 M field multiplications per chunk, almost all of them the discharge, so the lift does about 124 M. Against the SP1 lifter's 4.39 × 10^9-instruction guest at 219 responses:

| what is wrapped                               | multiplications | instructions (at 2,264 / 935 per mul) | against SP1 on ZKBoo |
| --------------------------------------------- | --------------: | ------------------------------------: | -------------------: |
| today's verifier                              |        ~124 M   | 2.8 × 10^11 / 1.2 × 10^11             |          64× / 26×   |
| uniform layout, discharge in closed form      |  ~6–24 M        | —  / 0.6–2.2 × 10^10                  |        — / 1.3–5×    |
| committed matrix (openings and memory checks) |   ~1.5 M        | —  / ~1.4 × 10^9                      |          — / ~0.3×   |

- These are lower bounds on instructions: they count only multiplications, and the other work is not measured.
- The middle row's range reflects the Keccak part, which the native verifier currently evaluates with about 9 M multiplications per chunk; the contract's algorithm needs far fewer.
- The project has recorded that instructions do not convert to seconds at a fixed rate between programs. At the SP1 lifter's own rate, about 1.2 M instructions per second on its GPU path, the last row would be roughly a quarter of an hour of SP1 proving, against the SP1 lifter's hour.

**Wrapping only beats running SP1 on ZKBoo directly once the matrix discharge has left the verifier (route 1).** Even then the result is a classical, BN254-bounded proof like the SP1 lifter's, with the Flock block's fidelity gap added and two provers to run. Its gain would be proving time, not security.

## Route 4: optimistic verification

Accept a lift unless someone challenges it, and settle a challenge by bisection down to one step that a contract re-executes.
- **Honest path.** The proof must be available: 1,215,008 bytes of calldata is 19.26 M gas (measured), over one transaction's cap, so it goes in blobs or in two transactions. Add one assertion with a bond. That is of the order of 10^5 gas plus data, with no verification at all unless someone disputes.
- **Dispute over the discharge.** The discharge is a fold over 2,718,991 records with a state of two field elements per claim, so it bisects in 22 rounds. A single record re-executed without the per-call tables costs at most 66 operands × 22 `eq` multiplications, about 2.6 M gas per claim, which fits a transaction.
- **Dispute over the rest.** The lift contract's phases carry a large state (transcript, Ligerito), so they suit a general-purpose fault-proof virtual machine better. That means running the native verifier as a RISC-V or MIPS program with an audited one-step verifier, as optimistic rollups do. At the portable multiplication cost the trace is about 2.8 × 10^11 steps, about 38 bisection levels. The per-move and per-step gas of existing one-step verifiers was not measured here.

This is the only route to ordinary transaction costs that stays hash-based, with no pairing and no BN254 ceiling. What it gives up:
- **finality:** a challenge window, typically days;
- **liveness:** at least one honest watcher has to exist;
- **economics:** a bond has to be designed.

Whether a delayed, contestable acceptance is acceptable for an emergency migration mechanism is a design decision for the project, not a measurement.

## What to do next, if anything

- **Uniform layout.** It is free for the prover and validated, but alone it only reaches about a tenth of today's gas. It is worth merging as the block's layout only if one of the other routes is pursued, since both route 1 (class-level commitments) and route 3 (native discharge in closed form) build on it.
- **Committed matrix.** It is the one structural route that could bring a direct verifier to about 2–3 B gas. Even that is about 150 transactions, so a direct verifier stays impractical on L1.
- **L1 deployment.** A deployable Flock-based path is either wrapping (after the committed matrix, and classical) or optimistic (hash-based, and delayed).
