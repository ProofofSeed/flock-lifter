# The WHIR wrapper

Status: built, validated and measured, 2026-10-05; gas reduced by a further fifth the same day.
A wrapped lift is one Flock proof that the lift's chunk proofs verify, opened with WHIR, plus a proof that the fixed structure this wrap proof refers to is the committed one.
Verifying it on chain for the 219-response hardened-child lift takes **68.62 M gas in 7 transactions**, each under the 2^24-gas cap (EIP-7825), with every contract under the 24,576-byte limit (EIP-170).
The same checks in one call, with both limits lifted, cost 65.85 M.
The staged direct route it sits beside takes 889.04 M gas in 106 transactions (`staged-verification.md`), so the wrapper costs a thirteenth of it.
Record: `fixtures/wrap-bench-2026-10-05-after-savings.summary.log`.
The first measurement was 88.08 M staged and 85.06 M in one call (`fixtures/wrap-bench-2026-10-05.summary.log`); "What changed" below lists what took it down.

Nothing here is audited, and the soundness accounting of the structure proof is this project's own (see Caveats).

## What is proved

**Chunks.** The lift proves its responses in chunks as before, on a BLAKE3 transcript (`crates/lift/src/chunk_wrap.rs`), with the chunks' openings merged.

**Wrap proof.** A Flock union circuit verifies every chunk proof (`crates/lift/src/wrap.rs`).
Its public segment holds the words the responses publish, so the native Fiat-Shamir gate reads them from the wrap proof.
It is proved on a Keccak-256 transcript and opened with WHIR over GF(2^128), with challenges in GF(2^256), folding factor 4, a final polynomial of 3 variables, the Johnson regime, 22 grinding bits and Keccak-256 Merkle trees (`crates/whir`).
Chunk domains are static, so one wrap key serves every statement of a shape.

**Structure proof.** Flock's deferred verifier leaves three kinds of prover-supplied values undischarged: the Boolean tables' and the element tables' matrix evaluations, and one wiring evaluation.
Evaluating the tables on chain is what made the earlier routes expensive.
Here the tables are committed once per shape as 2^27 bytes in GF(2^8) inside GF(2^128) (`crates/structure`), and each lift carries a proof that the reported evaluations are the committed tables': table folds, four sumchecks that leave eleven claims on the bytes' bits, a fifth sumcheck that batches those into one (`batch.rs`), and one WHIR opening.
Bits are read from bytes through eight Frobenius-conjugate openings, so the opening has 8 points; before the batching it had 88.

## The contract

`verifier/src/wrap/FlockWrap.sol` is the single-call reference; `verifier/src/wrap/staged/` is the deployable verifier.
A Rust mirror (`crates/evm/src/wrap/`) reads the same calldata, and the bench compares the contract's transcript with the mirror's at every stage boundary.

The contract takes the expected output, its word counts, the binding and the lift; the counts must be the statement circuit's (`WrapKey.COUNTS`), and the response count, the chunk size and the committed tables are constants of the key.

What the contract does, in order, with the single call's gas at 219 responses:

| step                                             | gas (M) |
| ------------------------------------------------ | ------: |
| Fiat-Shamir gate and binding the published words |    2.28 |
| Boolean zerocheck                                |    0.54 |
| union lincheck                                   |    0.54 |
| wiring product argument                          |    5.60 |
| element zerocheck and lincheck                   |    2.91 |
| ring switches                                    |    2.70 |
| multipoint assist and anchor                     |    0.53 |
| claim weights over squaring chains               |    3.61 |
| layout equation                                  |   10.71 |
| outer WHIR opening                               |    4.28 |
| outer opening's last equation                    |    4.91 |
| structure proof's folds and sumchecks            |    5.67 |
| bit claim's conjugates                           |    0.19 |
| tables' WHIR opening                             |    6.02 |
| tables' opening's last equation                  |    8.71 |
| calldata (432,088 B) and base cost               |    6.65 |

What keeps these small:
- **Field arithmetic.** A GF(2^128) product is 25 integer multiplications on operands split every fifth bit, about 590 gas inlined with lazy reduction, against 2,090 for the earlier routine. A GF(2^256) product costs about 2,250. The kernels are generated assembly (`verifier/tools/kernels.py` writes `K.sol`). No arrangement with fewer than 25 multiplications was found: five-bit spacing is what a 256-bit product can hold.
- **Sumchecks.** Round claims are kept as fractions, so no round inverts.
- **Frobenius sums.** A sum `Σ c_j v_j^(2^j)` is a squaring chain over `c_j^(2^-j)·v_j`. The `2^j`-th root of a coordinate is its `2^(128−j)`-th power, so the chain meets the roots in the order repeated squaring gives them, and the prover supplies nothing.
- **Closed forms.** The ring switches' linearised coefficients, the twisted equality polynomial, the layout's run weights and the boundary branching program are evaluated by recurrences, not tables over their domains.
- **WHIR's last equation.** A queried position contributes a product of factors `1 + y·w` with `y` a challenge in GF(2^256) and `w` in GF(2^128). Each factor is `κ·(u + t)` with `t` in GF(2^128), `u` the extension's generator and `κ` depending on the challenge alone. Multiplying by `u + t` costs two base-field products where a general product costs three, the `κ` are multiplied in once per round, and the constants come from one batched inversion per opening. The `t` are read from 4-bit windowed tables.
- **Layout equation.** A claim's layout weight is the extension, at its column point, of the runs' weights spread over their columns. It is folded directly, and a pair of equal neighbours folds without a product. The branching program's layers above the row variables are run once for the four claims.
- **Memory.** Solidity never frees memory and its cost grows quadratically, so the single call releases what a finished phase allocated. Its high-water mark is 620 KB.

## Stages

`WrapSessions` holds the Keccak-256 of each session's state per caller and salt, routes a call to one of seven stateless stage contracts, and records the hash of the state that comes back.
The state is an ABI-encoded bag (`staged/Carry.sol`) of 3 to 28 KB.
The last stage sets `accepted[digest]`.

| transaction | gas        | of the cap | work                                                          |
| ----------: | ---------: | ---------: | ------------------------------------------------------------- |
|           1 | 10,637,207 |      63.4% | gate, binding, zerocheck, lincheck, wiring                    |
|           2 | 10,344,848 |      61.7% | element class, ring switches, assist sumchecks, claim weights |
|           3 | 11,025,691 |      65.7% | layout equation                                               |
|           4 | 11,430,696 |      68.1% | outer opening                                                 |
|           5 |  6,601,500 |      39.3% | table folds and sumchecks, bit claims' batching               |
|           6 |  9,490,087 |      56.6% | bit claim's conjugates, tables' opening                       |
|           7 |  9,094,200 |      54.2% | tables' opening's last equation                               |

Deployment is 35.2 M gas over twelve contracts, the largest 23,164 B.
Six transactions would fit the gas cap, but no two neighbouring stages fit one contract under the code-size limit.

## Prover

Measured on the M4 Max, 219 responses, outer rate 2^-6, tables' rate 2^-4:

| phase                 | seconds |
| --------------------- | ------: |
| chunks                |    11.5 |
| wrap proof            |    16.9 |
| committing the tables |    10.5 |
| structure proof       |    33.1 |
| whole lift            |    72.2 |

Peak resident memory is 123.1 GB on a 137 GB machine, against 74.6 GB for the unwrapped lift at 13.4 s.
The tables' commitment is recomputed in every lift here, although it is fixed per shape.
At rate 2^-6 the tables' commitment was killed for memory, so the tables stay at 2^-4.
With both rates at 2^-1 the lift takes 29.6 s and 88.2 GB and is 815,659 B (`fixtures/acceptance-wrap-both-2026-10-05-after-savings.summary.log`); that shape was not measured on chain.

Two parameters trade proving time for gas:
- **Outer rate 2^-8.** 64.62 M in one call and 67.32 M staged, for a lift of 106.6 s (`fixtures/wrap-bench-2026-10-05-after-savings-outer-rate-8.summary.log`). That is 1.3 M for about 32 s. It was measured while the contract derived the public words' commitment (see Caveats), which cost about 16,000 gas more than the current binding.
- **Grinding.** 26 bits in place of 22 saved about 0.8 M for about 24 s more, measured once on an 8-response lift together with the rate above and not kept.

## What changed after the first measurement

Single-call gas at 219 responses went from 85.06 M to 65.85 M.
The steps were measured one at a time on an 8-response lift, whose single call went from 76.95 M to 59.45 M:

| change                                                        | saved (M) |
| ------------------------------------------------------------- | --------: |
| final polynomial of 3 variables in both openings              |      2.17 |
| normalised factors in the openings' last equations            |      3.48 |
| batching the bit claims before the tables' opening            |      4.86 |
| squaring chains without prover-supplied roots, cheaper levels |      2.60 |
| one-pass layout equation, shared boundary layers, releases    |      2.69 |
| layout weights by folding, gate first                         |      1.69 |

The batching also shortened the structure proof by about 20 s.
Skipping repeated blocks of public words saved a further 0.24 M at 219 responses, where a chunk is padded.

## Validation

- **Native acceptance.** `acceptance-wrap both`: the reject matrix R1 to R8, eleven wrap cases, four structure cases, a key reused across lifts, and a 219-response lift through the relying-party gate. All pass, before and after the gas savings. W10, a lift verified under a statement its key is not for, was accepted until the key and the statement were tied (`input-trust-review.md`).
- **Mirror.** `wrap-check` compares the Rust mirror with the native verifier; `wrap-bench` compares the contract with the mirror stage by stage, at 8 and at 219 responses.
- **Tampering.** 23 flipped bits across a lift are refused by the single call and 11 by the staged verifier.
- **Deletion.** Four checks can be singled out by one flipped bit: a WHIR opening's last equation, a Merkle path, the Fiat-Shamir gate, and the session's state comparison. For each, a case built to fail only that check is refused, and is accepted once the check is deleted, with every other case still refused (`fixtures/deletion-validation-2026-10-05-wrap-after-savings.summary.log`). That run predates the return to Flock's own binding of the public words, which touches none of the four checks.
- **Element tables.** With the comparison in `WrapPiop._elementTables` deleted, the shifted element-table evaluations of `crates/evm/tests/wrap_element.rs` are accepted by the single call and by the staged verifier, whose session then accepts the statement; with it in place, both revert with `ElementTable` (2026-11-11, 8 responses, not recorded under `fixtures/`).
- **After pinning the word counts.** The same run on 2026-10-09, with the contracts refusing any word counts but the key's, agrees with the mirror at every stage, refuses the same tampering, the three single-check cases and another split of the counts, and costs 192 gas less in one call (`fixtures/wrap-bench-2026-10-09-pinned-counts.summary.log`).
- **Limit of that method.** A flip anywhere else in a lift changes the transcript and fails a grinding check first, so the remaining contract checks are not individually validated by deletion. They are covered by agreement with the mirror and, natively, by the reject matrix and the structure crate's tests.

## Caveats

- **Not audited.** Neither the contracts nor the structure proof's soundness analysis.
- **Batch inversion.** The contract refuses an opening in which a challenge's upper half or norm is zero, which the native verifier would accept. Either has probability about 2^-128 per challenge.
- **Publics digest.** Flock absorbs a BLAKE3 digest of the public words. The contract takes that digest from calldata without recomputing it. The public words themselves are absorbed by the wrap's Keccak binding beforehand, so the digest adds nothing the transcript does not already hold, and a prover who varies it gains only what varying any other absorbed message gains. That argument has not been reviewed. A variant in which the transcript committed to the words under Keccak-256, so that the contract could derive the commitment, was built and then withdrawn, because upstream Flock would no longer verify the wrap proof. The derivation hashed the 82,736 bytes of public words (`NUM_PUBLIC` 5,171 × 16), about 15,500 gas, and withdrawing it lowered the single call by 16,373 gas (65,861,582 → 65,845,209 in `fixtures/wrap-bench-2026-10-05-after-savings.summary.log`, before and after). Recomputing the BLAKE3 chain on chain is estimated at about 15 M gas for the 83 KB of public words and was not built.
- **Security level.** The WHIR parameters target 128 bits including 22 bits of grinding in the Johnson regime. 219 responses is classical 128-bit in the forgery-work-ratio sense only. No post-quantum claim is made.
- **Lift fidelity.** Unchanged from the lifter: the block is a compilation of the ZKBoo verifier, checked differentially.
- **Shape.** Gas was measured for one statement at one size. The contracts compile and pass at 8 responses too.
- **Flock upstream.** Flock's non-deferred union-circuit verifier accepts shifted element matrix evaluations, since it only checks that they recombine. This lifter's verifiers compare them with the tables: natively (`shifted_element_matrix_evaluations_are_refused`), and on chain, where the single call and the staged verifier both revert with `ElementTable` (`crates/evm/tests/wrap_element.rs`). Other users of that verifier are exposed.

## Not done

- **Capacity-bound soundness.** WHIR's conjectured regime would roughly halve the queries of both openings. It rests on a conjecture, so it was not used.
- **Subfield codewords.** The tables' bytes lie in GF(2^8), so their codeword could live in GF(2^32) at a quarter of the memory, which would allow rate 2^-5 there. It needs a subfield transform in the prover. Estimated at 2 M; not measured.
- **Fewer transactions.** Regrouping the stages into six needs finer cuts than the present phase boundaries. Estimated at 0.4 M; not measured.
- **Packing the carried state.** Estimated at 0.4 M of staged gas; not measured.
- **High-degree sumchecks.** The structure proof's sumchecks have degrees up to 65, which costs about 2 M in messages and their evaluation. Lowering the degree means redesigning how the proof addresses its lists.

## Running it

```sh
cargo build --release -p pofseed-flock-lift-host -p pofseed-flock-lift-evm
./target/release/acceptance-wrap both       # native reject matrix and a full lift
./target/release/wrap-bench 219 128 6 4     # responses, chunk size, outer rate, tables' rate
python3 verifier/tools/kernels.py           # regenerate verifier/src/wrap/K.sol
```

`wrap-bench` caches lifts under `target/wrap-cache/`; `POFSEED_WRAP_FRESH=1` rebuilds one.
It writes `verifier/src/wrap/WrapKey.sol` for the shape it runs and restores the file afterwards unless `POFSEED_WRAP_KEEP` is set.
The committed key is the 219-response one.
