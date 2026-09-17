# TODO

Open work on the on-chain verifier, in the order it is worth doing.
Figures are for the 219-response hardened-child lift, from `fixtures/evm-bench-2026-09-16-committed-final.summary.log` unless stated; `knowledge/committed-matrix.md` has the context.
The direct route (`FlockLift` then `FlockMatrix`) costs 1,265.9 M gas, at least 76 transactions at the 2^24-gas cap.

## Verifier optimisation

- [ ] **Rewrite Ligerito's final-level residuals in monolithic Yul.**
  - **Cost.** The ring-switch and consistency residuals of the three openings (two chunks and the matrix) cost 187 + 126, 189 + 126 and 66 + 120 M gas: 814 M of the 1,266 M.
  - **Where it goes.** In the matrix opening, the ring-switch residual is 31 M of prefix-tensor work and 29 M of finishing over its 16 residual points. Both loops make table lookups through Solidity calls at about 220 gas each, where an inline Yul lookup costs about 50.
  - **The consistency residual** is about 20 GF(2^256) multiplications per stratified query, over roughly 435 queries per opening, in Solidity (`Opening.inducedBasis`).
  - **What to do.**
    - Port `Tensor.prefix`, `Tensor.finish` and the consistency residual to single assembly functions over pointer lists, as `Structured.sol` does.
    - Try 5- or 6-bit windows for the row-combination tables, which cost less to build than the current 8-bit ones.
    - Precompute the finishing map once per claim, instead of once per residual point.
  - **Done when** `evm-bench 219` shows the three residual pairs well below their current total, and `cargo test --release -p pofseed-flock-lift-evm` still passes.
- [ ] **Split verification into transactions and bind the calls to each other.**
  - **The problem.** `FlockLift.verify` (830.4 M) and `FlockMatrix.verify` (435.5 M) each run as one call with the gas cap lifted, so "at least 76 transactions" is a lower bound, not a protocol.
  - **What to do.**
    - Make each call resumable across transactions that fit 2^24 gas, carrying its state by hash.
    - Have the lift contract commit its packed claims and statement digest in storage, so the matrix contract reads them instead of taking them as arguments.
  - **Done when** a whole verification runs as a measured sequence of capped transactions, and a matrix call on claims the lift contract did not produce is refused.
  - **Note.** The optimistic route (`knowledge/optimistic-verification.md`) already fits every transaction under the cap, but it does so by dispute, not by direct verification.
- [ ] **Bring the contracts under EIP-170.**
  - **The problem.** The runtime code of `FlockLift` is 94,320 bytes and that of `FlockMatrix` 94,197, against the 24,576-byte limit; the harness lifts the limit.
  - **What to do.** Most of the size is generated constants (`Constants.sol`: subspace table, φ₈ nodes, Ligerito schedules) and linked library code. Move the tables into separate data contracts read with `EXTCODECOPY`, and split the libraries into deployed contracts called with `DELEGATECALL`.
  - **Done when** every deployed contract is under the limit and the gas figures are re-measured with the limit enforced.
- [ ] **Measure the `Slim` profile on the committed path.**
  - **The gap.** `POFSEED_LIGERITO_PROFILE=slim` was measured only with the row-walking discharge (lift contract 680.28 M against 830.28 M under `Fast`). It has not been run with the regular layout and the matrix contract, whose own opening is also profile-dependent.
  - **What to do.** Prove a 219-response lift under `Slim` into its own cache, run `evm-bench`, and add the row to `knowledge/performance-table.md`.
  - **Done when** the fixture exists and the table carries both profiles for the committed path.

## Optimistic route

- [ ] **Widen the heaviest dispute step's margin.**
  - **The problem.** The heaviest step of the dispute game is `FlockMatrix` copying the 4,738-word matrix proof in one `CALLDATACOPY`. Resolved in a game it costs 14.84 M gas, 1.94 M under the transaction cap (`knowledge/optimistic-verification.md`).
  - **Why it matters.** A verifier that copied more calldata at once could not be disputed at all.
  - **What to do.** Split large copies across machine steps, or have the verifier read the proof in pieces.
  - **Done when** the heaviest resolved step has a comfortable margin, re-measured with the dispute simulator.
