# flock-lifter

A succinct lifter for ZKBoo proofs of seed built on [Flock](https://github.com/succinctlabs/flock), Succinct's hash-based SNARK for batched Boolean computations: the verification of each ZKBoo response — its two-party view replay, the Keccak-256 PRG tapes and view commitments behind it — is compiled into one row of a Boolean R1CS table and proved with Flock's zerocheck, lincheck and Ligerito commitment, and the global Fiat-Shamir gate that ties the responses together runs natively over the words each row publishes.
It lifts the same statement under the same crypto suite as the companion SP1 lifter in `../sp1-lifter`, and ends in the same journal and relying-party gate, so the two can be compared on equal terms.
A lift can also be verified by EVM contracts, which are measured and not deployable: about 158 billion gas for a 219-response lift.

## Usage

Requires Rust 1.95.0 (pinned by `rust-toolchain.toml`) and local checkouts of the ZKBoo crates under `../../zkboo`, which are patched in at the workspace root because every published version is yanked.
Flock is pinned to a revision of its public repository and builds with `target-cpu=native`, as its kernels expect.

```sh
cargo build --release -p pofseed-flock-lift-host
./target/release/acceptance both            # reject matrix, then a full 219-response lift through the gate
./target/release/chunk-probe 128 row-major  # one Flock proof over 128 responses, timed
./target/release/statement-profile          # gate counts and response size of the lifted statement
cargo test --release -p pofseed-flock-lift-block -p pofseed-flock-lift   # differential and end-to-end tests
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

The EVM verifier needs Foundry (`forge`, looked up at `~/.foundry/bin/forge`); the harness builds `verifier/` itself.

```sh
cargo build --release -p pofseed-flock-lift-evm
./target/release/evm-bench 219 /tmp/lift-219.bin   # gas per phase of verifying a lift on chain
./target/release/evm-constants                     # regenerate verifier/src/Constants.sol
./target/release/row-shapes                        # how regular the block's rows are
cargo test --release -p pofseed-flock-lift-evm     # contracts against the Rust mirror and the native discharge
```

Set `POFSEED_TIMING=1` for the lifter's own phase timings; Flock's `PCS_TRACE`, `FLOCK_ZC_TIMING` and `LINCHECK_TRACE` break down the rest.
`POFSEED_LIGERITO_PROFILE=slim` proves at rate 1/4 instead of 1/2: a third off the proof for about a sixth more proving work.

## Structure

- `crates/statement/` — the proof-of-seed circuit, the fixed Keccak-256 crypto suite, and the lifted journal with its relying-party gate.
- `crates/block/` — the response block: the symbolic compiler of a ZKBoo circuit's two-party replay (`replay`), the Keccak-f sub-block encoding (`keccak`), the block geometry (`layout`), and the program that generates a response's witness, folds the block's lincheck for the prover and discharges the verifier's matrix claims from the block's structure (`program`).
- `crates/lift/` — Flock proofs over batches of response blocks (`chunk_rm`, the row-major path the lift uses; `chunk`, the union circuit path it replaced) and the whole-proof lift with its native Fiat-Shamir gate (`lift`).
- `crates/host/` — proof generation, the acceptance run and the probes.
- `crates/evm/` — the EVM side: calldata encoding of a lift, a Rust mirror of the contract verifier, the discharge stream, and an in-process EVM harness with the gas benchmark.
- `verifier/` — the Solidity verifier (Foundry): `FlockLift` verifies every chunk and the Fiat-Shamir gate, and `FlockDischarge` evaluates the resulting matrix claims from a hash-pinned stream of the block's rows.
- `knowledge/` — design record and measurements; `design.md` explains the block and why the lift proves it through the row-major path, `matrix-discharge.md` how the verifier checks the lincheck's last equation without a vector over the block's columns, and `evm-verifier.md` what verifying a lift on Ethereum costs and why it is not deployable.
