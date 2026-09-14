# flock-lifter

A succinct lifter for ZKBoo proofs of seed built on [Flock](https://github.com/succinctlabs/flock), Succinct's hash-based SNARK for batched Boolean computations: the verification of a ZKBoo proof — the two-party view replay of every response, the Keccak-256 PRG tapes and view commitments behind it, and the global Fiat-Shamir gate — is expressed as a batch of Boolean R1CS instances, one per response, and proved with Flock's zerocheck, lincheck and Ligerito polynomial commitment.
It lifts the same statement, under the same crypto suite, as the companion SP1 lifter in `../sp1-lifter`, so that the two can be compared on equal terms.

## Usage

Requires Rust 1.95.0 (pinned by `rust-toolchain.toml`) and local checkouts of the ZKBoo crates under `../../zkboo`, which are patched in at the workspace root because every published version is yanked.
Flock is pinned to a revision of its public repository.

```sh
cargo build --release -p pofseed-flock-lift-host
./target/release/statement-profile   # gate counts and response size of the lifted statement
./target/release/flock-spike         # a toy Boolean table through Flock's circuit path
```

## Structure

- `crates/statement/` — the proof-of-seed circuit and the fixed Keccak-256 crypto suite, shared by prover and verifier.
- `crates/host/` — proof generation, and the proving and verification drivers.
- `knowledge/` — design record and measurements.
