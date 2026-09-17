# flock-lifter

A succinct lifter for ZKBoo proofs of seed built on [Flock](https://github.com/succinctlabs/flock), Succinct's hash-based SNARK for batched Boolean computations: the verification of each ZKBoo response — its two-party view replay, the Keccak-256 PRG tapes and view commitments behind it — is compiled into one row of a Boolean R1CS table and proved with Flock's zerocheck, lincheck and Ligerito commitment, and the global Fiat-Shamir gate that ties the responses together runs natively over the words each row publishes.
It lifts the same statement under the same crypto suite as the companion SP1 lifter in `../sp1-lifter`, and ends in the same journal and relying-party gate, so the two can be compared on equal terms.
On Ethereum, a lift can be accepted in two ways, both built and measured on a 219-response lift:
- **Direct verification** runs the EVM verifier on chain: a lift session, then a matrix session bound to the claims it recorded, with the block's explicit rows discharged by a proof against an entry list committed once per statement. Every transaction fits mainnet's gas cap and every contract its code-size limit; at 219 responses it takes 889 million gas in 106 transactions under the `Fast` profile (781 million in 100 under `Slim`). The same checks as two single calls, with the limits lifted, cost 759 million.
- **Optimistic verification** accepts the lift unless someone disputes it. An asserter uploads the proofs and posts a bond, and a dispute is settled by bisecting the direct verifier's own execution down to one EVM step, which a contract re-executes. It costs 64 million gas when unchallenged. Within a dispute, no transaction costs more than 7 million gas, well under the 2^24 gas cap.

## Usage

Requires Rust 1.95.0 (pinned by `rust-toolchain.toml`) and local checkouts of the ZKBoo crates under `../../zkboo`, which are patched in at the workspace root because every published version is yanked.
Flock is pinned to a revision of its public repository and builds with `target-cpu=native`, as its kernels expect.

```sh
cargo build --release -p pofseed-flock-lift-host
./target/release/acceptance both            # reject matrix, then a full 219-response lift through the gate
./target/release/chunk-probe 128 row-major  # one Flock proof over 128 responses, timed (add `compact` for the old layout)
./target/release/statement-profile          # gate counts and response size of the lifted statement
cargo test --release -p pofseed-flock-lift-block -p pofseed-flock-lift   # differential and end-to-end tests
cargo test --release -p pofseed-flock-lift --features forgery --test matrix # the matrix proof against forging provers
cargo test --release -p pofseed-flock-lift-block --test block -- --ignored # the hardened-child block at full size
```

```sh
./target/release/verifier-cost 128            # what a chunk proof is made of
cargo run --release -p pofseed-flock-lift-host --features count --bin verifier-cost -- 128
                                              # ...and what verifying it costs, per phase
./target/release/block-stats                  # the block's shape and sparsity
./target/release/verify-only prove 219 /tmp/lift.bin   # then `check`, to time and measure the
./target/release/verify-only check 219 /tmp/lift.bin   # verifier without the prover around it
```

Both on-chain routes need Foundry (`forge`, looked up at `~/.foundry/bin/forge`); the harnesses build `verifier/` themselves.
Direct verification:

```sh
cargo build --release -p pofseed-flock-lift-evm
./target/release/evm-bench 219 /tmp/lift-219.bin   # gas per phase in two single calls, then per stage in capped transactions
POFSEED_EVM_DISCHARGE=stream ./target/release/evm-bench 219 /tmp/lift-219.bin   # ...walking the rows instead
./target/release/evm-constants                     # regenerate verifier/src/Constants.sol
python3 verifier/tools/residual.py                 # regenerate verifier/src/Residual.sol
./target/release/row-shapes                        # how regular the block's rows are
./target/release/layout-probe                      # how far they collapse into classes, by layout
cargo test --release -p pofseed-flock-lift-evm     # contracts against the Rust mirror and the native discharge
```

Optimistic verification, over the same two calls:

```sh
cargo build --release -p pofseed-flock-lift-optimistic
./target/release/dispute-sim 219 /tmp/lift-219.bin 16   # upload, assert, confirm, and 13 disputes played to the end;
                                                        # a fourth argument lists steps to resolve in games of their own
./target/release/dispute-costs 219 /tmp/lift-219.bin 237058466   # per-move gas by arity, the unchallenged path
./target/release/onestep-check 219 /tmp/lift-219.bin    # the one-step contract against revm on the real trace
./target/release/trace-stats 219 /tmp/lift-219.bin      # the trace's length and its largest steps
./target/release/onestep-fuzz 3000                      # ...and on random programs
cargo test --release -p pofseed-flock-lift-optimistic   # disputes on stand-in contracts, forged witnesses, a fuzz campaign
```

Set `POFSEED_TIMING=1` for the lifter's own phase timings; Flock's `PCS_TRACE`, `FLOCK_ZC_TIMING` and `LINCHECK_TRACE` break down the rest.
`POFSEED_LIGERITO_PROFILE=slim` proves at rate 1/4 instead of 1/2: measured on a 128-response chunk, 35.4% off the chunk proof for 20% more proving time (`knowledge/performance-table.md`).

## Structure

- `crates/statement/` — the proof-of-seed circuit, the fixed Keccak-256 crypto suite, and the lifted journal with its relying-party gate.
- `crates/block/` — the response block: the symbolic compiler of a ZKBoo circuit's two-party replay, in its regular and compact layouts (`replay`), the Keccak-f sub-block encoding and its rotation-invariant fold (`keccak`), the block geometry (`layout`), the program that generates a response's witness, folds the block's lincheck for the prover and evaluates the structured part of the verifier's matrix claims (`program`), and the explicit rows as a list of table-weighted entries (`committed`).
- `crates/lift/` — Flock proofs over batches of response blocks (`chunk_rm`, the row-major path the lift uses; `chunk`, the union circuit path it replaced), the proof that discharges their explicit rows against the committed entry list (`matrix`), and the whole-proof lift with its native Fiat-Shamir gate (`lift`).
- `crates/host/` — proof generation, the acceptance run and the probes.
- `crates/evm/` — the EVM side: calldata encoding of a lift and its matrix proof, a Rust mirror of the contract verifiers, the row stream, and an in-process EVM harness with the gas benchmark and the layout probes.
- `crates/optimistic/` — optimistic verification: the direct verifier's execution as a trace of committed EVM states, witnesses for any single step, the off-chain side of the dispute game, a simulation of whole disputes, and a fuzzer of the one-step contract against revm.
- `verifier/` — the Solidity verifier (Foundry). `src/staged/` holds the deployable verifier: `FlockSessions` advances lift and matrix sessions across transactions, through seven stage contracts. `FlockLift` verifies every chunk and the Fiat-Shamir gate in one call, and `FlockMatrix` discharges the resulting matrix claims, computing their Keccak part (`Structured`) and checking the matrix proof against the pinned entry commitment, and both evaluate Ligerito's final-level residuals in assembly (`Residual`, generated by `tools/residual.py`); `FlockDischarge` is the row-walking discharge it replaced. `src/optimistic/` holds the optimistic route: `OneStep` re-executes one step of those two calls, and `Dispute` runs uploads, assertions and games.
- `TODO.md` — the open work on the on-chain verifier, in order.
- `knowledge/` — design record and measurements; `design.md` explains the block and why the lift proves it through the row-major path, `matrix-discharge.md` how the verifier checks the lincheck's last equation without a vector over the block's columns, `evm-verifier.md` what verifying a lift on Ethereum first cost, `verifier-routes.md` the routes costed to cheapen it, `committed-matrix.md` the regular layout and committed matrix that were built, `staged-verification.md` how they run in transactions under mainnet's limits, and `optimistic-verification.md` the optimistic route beside it.
