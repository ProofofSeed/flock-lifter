# Moving to zkboo 1.3.0

Status: ported and re-measured, 2026-09-21.
Until then the workspace built only against zkboo 1.2.x, and every figure in this repository belonged to the 1.2.1 hardened-child circuit.
This file records what the release changed here, what was re-measured, and what was not.
The upstream account is each ZKBoo crate's `CHANGELOG.md`; the SP1 lifter's port is recorded in the `knowledge/zkboo-1.3.0-migration.md` of the `sp1-lifter` repository.

## What changed upstream, and here

- **BIP-32's validity conditions are asserted** (`zkboo-bip32`). `hardened_child_key` asserts `IL` below the group order and a non-zero child key, and takes the assertion accumulator it writes them to. `HardenedChildCircuit::exec` passes the scope's accumulator, so the assertion word the circuit emits now carries these conditions instead of being the constant 1.
- **A ZKBoo verifier must name the repetition count** (`zkboo`). Nothing here calls zkboo's `verify`: the lifter compiles the verifier into the response block, and the count is enforced where it always was, by `check_journal` and the relying party's gate. `n_eps` now delegates to `Repetitions::for_pq_security_bits` instead of carrying its own copy of the formula.
- **Requirements.** Every crate requires `1.3`; the workspace still patches the ZKBoo crates to the local checkouts.

## What moved

The hardened-child fingerprint moved from `0xbd121f6f…` to `0x72936f446cf7905dcd6e5bc4f66e583b479bd74b3e338b8ff6542cdd9b41938f`, the same value the SP1 lifter and the other consumers carry.
With it moved every chunk proof, the statement digest, the entry list and its commitment, and what both on-chain routes pin.
None of these is written into the sources: the contracts take them as constructor arguments, and `verifier/src/Constants.sol` regenerates unchanged.

The circuit and its block, from `statement-profile` and `block-stats`:

|                        |      1.2.1 |      1.3.0 |
| ---------------------- | ---------: | ---------: |
| u64 `bitand` gates     |      3,376 |      3,380 |
| u64 `carry` gates      |      3,068 |      3,076 |
| u8 `bitand` gates      |         10 |         13 |
| response size (B)      |     51,691 |     51,790 |
| PRG blocks per slot    |      1,613 |      1,616 |
| sponge blocks per slot |        380 |        381 |
| Keccak-f sub-blocks    |      3,988 |      3,996 |
| head sub-blocks        |        108 |        100 |
| replay rows            |  2,685,558 |  2,690,298 |
| explicit rows          |  9,481,178 |  9,499,510 |
| explicit nonzeros      | 55,601,381 | 55,657,945 |
| committed entries      |  3,059,456 |  3,062,361 |

The block stays at `k_log = 28` and the entry list at `2^22` entries, so no proof changes shape: every proof size in this repository is unchanged to the byte.

## Re-measured

All on 2026-09-21, M4 Max, one process at a time.

- **Tests.** The block's differential tests at full size (agreement with ZKBoo's native replay under every challenge, and the structured discharge against the dense fold), the lift's tests, the EVM tests (contracts against the Rust mirror, the staged verifier under both mainnet limits) and the optimistic tests all pass.
- **Acceptance** (`fixtures/acceptance-both-2026-09-21-zkboo-1.3.0.summary.log`): the reject matrix R1–R8 and F1–F8 refuses as before, and the 219-response lift passes the relying-party gate.
- **The lift** (`fixtures/lift-bench-2026-09-21-zkboo-1.3.0.summary.log`), 16 threads:

| responses | prove, 1.2.1 (s) | prove, 1.3.0 (s) | verify (s) | lifted proof (B) | peak RSS, 1.2.1 (GB) | peak RSS, 1.3.0 (GB) |
| --------: | ---------------: | ---------------: | ---------: | ---------------: | -------------------: | -------------------: |
|       128 |             7.45 |             7.25 |       0.01 |        1,063,686 |                64.78 |                64.63 |
|       219 |            13.30 |            13.40 |       0.02 |        1,675,231 |                74.77 |                74.61 |
|       438 |            23.99 |            23.75 |       0.02 |        2,892,929 |                79.70 |                79.54 |

  The 1.2.1 column is `fixtures/lift-bench-2026-09-16-committed-matrix.summary.log`. The differences are within run-to-run spread, and one run per row is not enough to attribute them to the release.

- **Direct verification** (`fixtures/evm-bench-2026-09-21-zkboo-1.3.0-{fast,slim}.summary.log`):

|                         | 1.2.1, `Fast` | 1.3.0, `Fast` | 1.2.1, `Slim` | 1.3.0, `Slim` |
| ----------------------- | ------------: | ------------: | ------------: | ------------: |
| single calls (M gas)    |        758.95 |        759.04 |        648.79 |        648.65 |
| staged (M gas)          |        888.96 |        889.04 |        780.99 |        780.85 |
| staged transactions     |           106 |           106 |           100 |           100 |
| largest transaction (M) |         16.57 |         16.57 |         16.55 |         16.55 |

  The residuals' cost depends on the opened values, which is where the ±0.03% comes from.
  The staged lift's recorded claim hash again equals the single-call contract's output, and the matrix session ends accepted.

- **Optimistic verification** (`fixtures/optimistic-*-2026-09-21-zkboo-1.3.0.summary.log`), with `OneStep` reading its pins from the held code (`optimistic-verification.md`):

|                                |       1.2.1 |       1.3.0 |
| ------------------------------ | ----------: | ----------: |
| trace (steps)                  | 237,058,466 | 237,087,171 |
| heaviest step, resolved (gas)  |   6,960,415 |   6,960,055 |
| unchallenged path (gas)        |  63,677,977 |  63,677,857 |
| deployment (gas)               |  44,724,642 |  44,730,170 |
| one-step checks, mismatches    |   50,432, 0 |   50,432, 0 |
| games won by the truthful side |       16/16 |       16/16 |

## Not re-measured

- The rows of `performance-table.md` other than those above, and every dated record in the other documents (`committed-matrix.md`, `verifier-routes.md`, `evm-verifier.md`, `matrix-discharge.md`), stay figures of the 1.2.1 circuit. The shapes they describe moved by less than 0.2%, as the table above shows.
- The deletion validations of 2026-09-14 to 2026-09-17 were not repeated; the checks they validated are unchanged.
- The comparison with the SP1 lifter uses SP1's 3,613.03 s, a zkboo 1.2.0 figure: its full-soundness lift has not been re-timed on 1.3.0.
