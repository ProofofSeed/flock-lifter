# verifier

The Solidity side of the Flock lifter: the contracts that verify a lifted proof on Ethereum, directly, optimistically or through the WHIR wrapper, built with Foundry (`forge build`) and exercised from Rust.

## What can be deployed

EIP-170 limits a contract's runtime code to 24,576 bytes.
Three contracts exceed it, so none of them can be deployed on mainnet:

| contract        | runtime (B) | role                                                                                |
| --------------- | ----------: | ----------------------------------------------------------------------------------- |
| `FlockLift`     |      53,351 | reference for the staged verifier, and the optimistic route's lift program          |
| `FlockMatrix`   |      53,899 | reference for the staged verifier, and the optimistic route's matrix program        |
| `FlockVerifier` |      47,510 | one chunk proof up to its matrix discharge; a test subject for `crates/evm/tests`   |

What each route deploys:
- **Direct verification** deploys `src/staged/`: `FlockSessions`, seven stage contracts and one data contract holding the subspace table, all under the limit (largest 22,893 B). `crates/evm/src/staged.rs` deploys and drives them; see `knowledge/staged-verification.md`.
- **Optimistic verification** deploys `Store`, the data contracts holding the runtime code of `FlockLift` and `FlockMatrix` in 24,000-byte chunks, `OneStep` (18,104 B) and `Dispute`. The two programs are never deployed: their runtime code is produced off chain, and `OneStep` reads the statement and parameters they pin from that held code. See `knowledge/optimistic-verification.md`.

- **Wrapped verification** deploys `src/wrap/staged/`: `WrapSessions`, seven stage contracts and four data contracts, all under the limit (largest 23,164 B). `crates/evm/src/wrap/staged.rs` deploys and drives them; see `knowledge/whir-wrapper.md`. `FlockWrap` (114,036 B) is their single-call reference and is never deployed. `src/wrap/` compiles under its own profile in `foundry.toml`, through the IR pipeline, which leaves the other contracts' bytecode unchanged.

`FlockDischarge` (22,586 B) fits, but it is the row-walking discharge the committed matrix replaced, at 158 billion gas for a 219-response lift (`knowledge/evm-verifier.md`).
`forge build --sizes` prints every contract's margin.

Every route fixes its statement at deployment: `FlockLift` and `LiftStages` take the circuit fingerprint, chain code, index, minimum response count and the expected output's word counts as constructor arguments, and the wrap's `WrapKey` is generated per statement and lift shape. A caller supplies only the expected output, its word counts, the binding and the proof, and the counts must be the pinned ones.

The single-call harness (`crates/evm/src/evm.rs`, `Evm::new`) lifts the code-size limit and the gas cap so the references can run; `Evm::mainnet` and the optimistic route's `Machine` keep the code-size limit.

## Tests

There are no Solidity tests.
Every contract is exercised from Rust in revm, against the native verifier or a Rust mirror of it:
- `crates/evm/tests/`: the chunk verifier against the mirror (`contract.rs`, `mirror.rs`), the lift contract and its Fiat-Shamir gate on forgeries, the matrix contract on tampering (`matrix.rs`), the row-walking discharge (`discharge.rs`), the field arithmetic (`gf2.rs`), the assembly residuals against their reference (`residual.rs`), the structured fold in pieces (`structured.rs`), and the staged verifier end to end under both mainnet limits with its refusals (`staged.rs`).
- `crates/optimistic/tests/optimistic.rs`: disputes played to the end, forged witnesses, and `OneStep` against revm on random programs.
- `crates/evm/tests/wrap_field.rs`: the wrap verifier's field kernels.
- The binaries `evm-bench`, `onestep-check` and `dispute-sim` repeat these checks at 219 responses.
- The wrap contracts are exercised by the binary `wrap-bench` only: against the Rust mirror stage by stage, under both mainnet limits, with tampered lifts and session states, at 8 and at 219 responses.

Several checks were validated by deletion: the check is removed and the test must fail (`fixtures/deletion-validation-*.summary.log`).

## Audit status

None of these contracts has been audited: not the staged verifiers and their session contracts, not `OneStep` and `Dispute`, not the wrap verifier or the structure proof it checks, and not the soundness accounting of the matrix proof they verify.
The evidence is the tests above, agreement with the native verifier, and fuzzing, which show that the contracts accept what the native verifier accepts and refuse the forgeries that were tried.
They are not a proof of soundness, and the contracts are not for production.
