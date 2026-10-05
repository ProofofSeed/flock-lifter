# The WHIR wrapper

Status: built, validated and measured, 2026-10-05.
A wrapped lift is one Flock proof that the lift's chunk proofs verify, opened with WHIR, plus a proof that the fixed structure this wrap proof refers to is the committed one.
Verifying it on chain for the 219-response hardened-child lift takes **88.08 M gas in 7 transactions**, each under the 2^24-gas cap (EIP-7825), with every contract under the 24,576-byte limit (EIP-170).
The same checks in one call, with both limits lifted, cost 85.06 M.
The staged direct route it sits beside takes 889.04 M gas in 106 transactions (`staged-verification.md`), so the wrapper costs a tenth of it.
Record: `fixtures/wrap-bench-2026-10-05.summary.log`.

Nothing here is audited, and the soundness accounting of the structure proof is this project's own (see Caveats).

## What is proved

**Chunks.** The lift proves its responses in chunks as before, on a BLAKE3 transcript (`crates/lift/src/chunk_wrap.rs`), with the chunks' openings merged.

**Wrap proof.** A Flock union circuit verifies every chunk proof (`crates/lift/src/wrap.rs`).
Its public segment holds the words the responses publish, so the native Fiat-Shamir gate reads them from the wrap proof.
It is proved on a Keccak-256 transcript and opened with WHIR over GF(2^128), with challenges in GF(2^256), folding factor 4, the Johnson regime, 22 grinding bits and Keccak-256 Merkle trees (`crates/whir`).
Chunk domains are static, so one wrap key serves every statement of a shape.

**Structure proof.** Flock's deferred verifier leaves three kinds of prover-supplied values undischarged: the Boolean tables' and the element tables' matrix evaluations, and one wiring evaluation.
Evaluating the tables on chain is what made the earlier routes expensive.
Here the tables are committed once per shape as 2^27 bytes in GF(2^8) inside GF(2^128) (`crates/structure`), and each lift carries a proof that the reported evaluations are the committed tables': table folds, four sumchecks and one multi-point WHIR opening.
Bits are read from bytes through eight Frobenius-conjugate openings.

## The contract

`verifier/src/wrap/FlockWrap.sol` is the single-call reference; `verifier/src/wrap/staged/` is the deployable verifier.
A Rust mirror (`crates/evm/src/wrap/`) reads the same calldata, and the bench compares the contract's transcript with the mirror's at every stage boundary.

What the contract does, in order, with the single call's gas at 219 responses:

| step                                             | gas (M) |
| ------------------------------------------------ | ------: |
| binding the published words                      |    1.29 |
| Boolean zerocheck                                |    0.54 |
| union lincheck                                   |    0.54 |
| wiring product argument                          |    5.84 |
| element zerocheck and lincheck                   |    2.91 |
| ring switches                                    |    2.70 |
| multipoint assist and anchor                     |    0.53 |
| claim weights over square-root chains            |    5.69 |
| layout weights and boundary values               |   10.80 |
| layout equation                                  |    3.71 |
| outer WHIR opening                               |    5.92 |
| outer opening's last equation                    |    6.37 |
| structure proof's folds and sumchecks            |    5.69 |
| bit claims' conjugates                           |    1.53 |
| tables' WHIR opening                             |    8.20 |
| tables' opening's last equation                  |   14.17 |
| Fiat-Shamir gate over the responses              |    1.29 |
| calldata (478,248 B) and base cost               |    7.34 |

What keeps these small:
- **Field arithmetic.** A GF(2^128) product is 25 integer multiplications on operands split every fifth bit, about 590 gas inlined with lazy reduction, against 2,090 for the earlier routine. A GF(2^256) product costs about 2,250. The kernels are generated assembly (`verifier/tools/kernels.py` writes `K.sol`).
- **Sumchecks.** Round claims are kept as fractions, so no round inverts.
- **Frobenius sums.** A sum `Σ c_j v_j^(2^j)` is a squaring chain over `c_j^(2^-j)·v_j`. The prover supplies the square roots and the contract checks each by one squaring.
- **Closed forms.** The ring switches' linearised coefficients, the twisted equality polynomial, the layout's run weights and the boundary branching program are evaluated by recurrences, not tables over their domains.
- **WHIR's last equation.** The queried positions' terms use 4-bit windowed tables per round.

## Stages

`WrapSessions` holds the Keccak-256 of each session's state per caller and salt, routes a call to one of seven stateless stage contracts, and records the hash of the state that comes back.
The state is an ABI-encoded bag (`staged/Carry.sol`) of 9 to 42 KB.
The last stage sets `accepted[digest]`.

| transaction | gas        | of the cap | work                                                          |
| ----------: | ---------: | ---------: | ------------------------------------------------------------- |
|           1 | 10,887,536 |      64.9% | gate, binding, zerocheck, lincheck, wiring                    |
|           2 | 12,974,852 |      77.3% | element class, ring switches, assist sumchecks, claim weights |
|           3 | 11,066,137 |      66.0% | layout weights and boundary values                            |
|           4 | 11,843,173 |      70.6% | layout equation, outer opening                                |
|           5 | 12,970,023 |      77.3% | outer opening's last equation, table folds and sumchecks      |
|           6 | 13,465,468 |      80.3% | bit claims' conjugates, tables' opening                       |
|           7 | 14,871,964 |      88.6% | tables' opening's last equation                               |

Deployment is 35.3 M gas over twelve contracts, the largest 23,896 B.

## Prover

Measured on the M4 Max, 219 responses, outer rate 2^-6, tables' rate 2^-4:

| phase                 | seconds |
| --------------------- | ------: |
| chunks                |    12.1 |
| wrap proof            |    16.5 |
| committing the tables |    10.4 |
| structure proof       |    56.2 |
| whole lift            |    95.4 |

Peak resident memory is 120.4 GB on a 137 GB machine, against 74.6 GB for the unwrapped lift at 13.4 s.
The tables' commitment is recomputed in every lift here, although it is fixed per shape.
At rate 2^-6 the tables' commitment was killed for memory, so the tables stay at 2^-4.
With both rates at 2^-1 the lift takes 43.2 s and 88.2 GB and is 827,003 B (`fixtures/acceptance-wrap-both-2026-10-05-22-bit-grinding.summary.log`); that shape was not measured on chain.

## Validation

- **Native acceptance.** `acceptance-wrap both`: the reject matrix R1 to R8, nine wrap cases, four structure cases, a key reused across lifts, and a 219-response lift through the relying-party gate. All pass.
- **Mirror.** `wrap-check` compares the Rust mirror with the native verifier; `wrap-bench` compares the contract with the mirror stage by stage, at 8 and at 219 responses.
- **Tampering.** 23 flipped bits across a lift are refused by the single call and 11 by the staged verifier.
- **Deletion.** Four checks can be singled out by one flipped bit: a WHIR opening's last equation, a Merkle path, the Fiat-Shamir gate, and the session's state comparison. For each, a case built to fail only that check is refused, and is accepted once the check is deleted, with every other case still refused (`fixtures/deletion-validation-2026-10-05-wrap.summary.log`).
- **Limit of that method.** A flip anywhere else in a lift changes the transcript and fails a grinding check first, so the remaining contract checks are not individually validated by deletion. They are covered by agreement with the mirror and, natively, by the reject matrix and the structure crate's tests.

## Caveats

- **Not audited.** Neither the contracts nor the structure proof's soundness analysis.
- **Publics digest.** Flock absorbs a BLAKE3 digest of the public words. The contract takes that digest from calldata without recomputing it. The public words themselves are absorbed by the wrap's Keccak binding beforehand, which is what the argument for this rests on; it has not been reviewed.
- **Security level.** The WHIR parameters target 128 bits including 22 bits of grinding in the Johnson regime. 219 responses is classical 128-bit in the forgery-work-ratio sense only. No post-quantum claim is made.
- **Lift fidelity.** Unchanged from the lifter: the block is a compilation of the ZKBoo verifier, checked differentially.
- **Shape.** Gas was measured for one statement at one size. The contracts compile and pass at 8 responses too.
- **Flock upstream.** Flock's non-deferred union-circuit verifier accepts shifted element matrix evaluations, since it only checks that they recombine. This lifter's verifier compares them with the tables (`shifted_element_matrix_evaluations_are_refused`). Other users of that verifier are exposed.

## Not done

Ideas costed but not built, with estimated savings on the single call: packing the carried state (0.4 M), trimming the square-root chains (0.6 M), weighing layout types in blocks (0.75 M), an outer rate of 2^-8 (1.6 M for about 10 s more proving), and codewords over a GF(2^32) subfield for the tables, which would allow a lower rate there.
None of these estimates is measured.

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
