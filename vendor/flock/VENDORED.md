# Vendored Flock

A copy of the crates of [Flock](https://github.com/succinctlabs/flock) at revision `b684b1258e4b1f202bec24afd660ace851b09e5e`, licensed MIT OR Apache-2.0 (see `LICENSE-MIT` and `LICENSE-APACHE`).

- The crates' manifests no longer inherit from Flock's workspace manifest, which is not vendored: the inherited package fields, dependencies and lints are written out in each crate.
- `rustfmt.toml` keeps Flock's default formatting when the repository's formatter runs.
- Every other change to the vendored sources is listed below.

## Changes

- `flock-core/src/pcs/outer.rs` (new): the `OuterPcs` trait, a commitment scheme over the dense stack that opens one point.
- `flock-core/src/pcs.rs`: `MergedOpenProof::inner` is a `MergedInner`, either Ligerito's opening or an outer commitment's bytes; `open_batch_merged` and `verify_batch_merged{,_deferred}` take an optional `OuterPcs`, which replaces Ligerito for the merged point.
- `flock-core/src/verifier.rs`: `verify_union_circuit{,_ag}_with_outer` and `verify_union_circuit{,_ag}_deferred_with_outer`, the RS and AG circuit verifiers with an optional `OuterPcs`.
- `flock-prover/src/prover.rs`: `prove_union_circuit{,_ag}_with_outer`, the RS and AG circuit provers with an optional `OuterPcs`, which then commits to the dense stack in place of Ligerito.
- The tower and tests reach Ligerito's opening through `MergedInner::ligerito_opening{,_mut}`.
- `flock-prover/src/tower/rowmajor.rs` (new): the in-circuit verifier of a row-major proof opened through the merged transport, and the wrap that proves many of them in one circuit proof (`prove_wrap`, `verify_wrap`), re-exported from `tower`.
  Unlike the tower's own child regions, it arithmetises the zerocheck (round-one interpolations, rounds, final product), both ring-switch claim checks and every grinding check, and derives Ligerito's per-query weights in-circuit rather than taking them as advice.
- `flock-prover/src/tower/whir_circuit.rs` (new): the in-circuit verifier of a `flock-whir` opening, driven by a recorded verification (`WhirRecord`, `build_whir_circuit`), re-exported from `tower`.
- `flock-prover/src/tower/head_walker.rs` (new): the in-circuit verifier of a union-circuit proof opened through WHIR (a wrap or head proof), adapted from `real_walker.rs` with the WHIR verifier in place of Ligerito's query phase, spine and residual, and with its zerocheck and ring-switch claim checks arithmetised; `build_head_circuit` builds and runs it standalone.
- `flock-prover/src/tower/head_env.rs` (new): the envelope wraps and heads share (slot list, row counts, public layout, constant table), its fitting from circuit censuses, and the key, proof and prover of a circuit built to it.
- `flock-prover/src/tower/head_step.rs` (new): the recursive lift and head: circuit proofs that a wrap, or a previous lift or head and a new wrap, verify, folding their deferred claims positionally into the accumulators they publish (`prove_head`, `verify_head`, and `prove_head_forging_route`, the adversarial leg the tests run).
- `flock-prover/src/tower/rowmajor.rs`: the wrap is built to an envelope, holds its chunks' R1CS digest in-circuit and publishes its block digest and lincheck accumulators as a head block; its fold tape and fold emitter are shared with the head.
- `flock-prover/src/tower/head_walker.rs`: the region also returns the child's registry-digest and row-count wires.
- `flock-core/src/circuit/builder.rs`: `ShapeBuilder::wire_used`.
- `flock-core/src/circuit.rs`: `Circuit::fixed_public`.
- `flock-core/src/matrix_fold.rs`: `prove_fold_with_grinding_owned`, the fold prover consuming its column marginals.
- `flock-prover/src/tower/query.rs`: `LeafOuter::shape` is shared behind an `Arc`.
- `flock-core/src/circuit.rs`: the circuit-structure matrix's row and column marginals run per plane and in parallel, and `CircuitStructureMatrix::col_marginals` computes several column marginals in one pass (results unchanged, checked against the entry-wise sums in `wiring_sigma_deferral`).
- `flock-core/src/matrix_fold.rs`: the fold prover's round message, low-variable fold, weight materialisation and μ-combination run in parallel (transcript unchanged).
- `flock-prover/src/tower/fold_region.rs`: `FoldLoc`'s ordinals are visible to the rest of the tower.
- `flock-prover/src/tower/child_walker.rs`: `ChildSlots::new` and the gate imports it needs are no longer test-only, and the constructor with a second BLAKE3 slot is visible to the tower.

## Known upstream failures

- `circuit_wiring::gather_claims_are_bound_by_the_opening` fails at this revision, unmodified, on replaying the element PIOP without its grinding nonces.
