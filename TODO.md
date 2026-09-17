# TODO

Open work on the on-chain verifier, in the order it is worth doing.
Figures are for the 219-response hardened-child lift, from `fixtures/evm-bench-2026-09-16-committed-final.summary.log` unless stated; `knowledge/committed-matrix.md` has the context.
The direct route now runs as a lift session and a matrix session, in 106 transactions under the 2^24-gas cap, for 889.2 M gas (`fixtures/evm-bench-2026-09-17-staged-fast.summary.log`); the same checks as two single calls with the cap lifted cost 759.1 M, and cost 1,265.9 M before the first item below.

## Verifier optimisation

- [x] **Rewrite Ligerito's final-level residuals in monolithic Yul.**
  - **Cost.** The ring-switch and consistency residuals of the three openings (two chunks and the matrix) cost 187 + 126, 189 + 126 and 66 + 120 M gas: 814 M of the 1,266 M.
  - **Where it goes.** In the matrix opening, the ring-switch residual is 31 M of prefix-tensor work and 29 M of finishing over its 16 residual points. Both loops make table lookups through Solidity calls at about 220 gas each, where an inline Yul lookup costs about 50.
  - **The consistency residual** is about 20 GF(2^256) multiplications per stratified query, over roughly 435 queries per opening, in Solidity (`Opening.inducedBasis`).
  - **What to do.**
    - Port `Tensor.prefix`, `Tensor.finish` and the consistency residual to single assembly functions over pointer lists, as `Structured.sol` does.
    - Try 5- or 6-bit windows for the row-combination tables, which cost less to build than the current 8-bit ones.
    - Precompute the finishing map once per claim, instead of once per residual point.
  - **Done when** `evm-bench 219` shows the three residual pairs well below their current total, and `cargo test --release -p pofseed-flock-lift-evm` still passes.
  - **Done** (2026-09-17): `verifier/src/Residual.sol`. The three residual pairs cost 51.2 + 64.5, 51.7 + 64.6 and 23.7 + 52.3 M, 307.9 M in all against 812.9 M, and verification 758.3 M (`fixtures/evm-bench-2026-09-17-residuals-fast.summary.log`). The EVM test suite passes, with a new test comparing both routines to the ones they replaced. Windows of 5 or 6 bits came out no cheaper than unrolled 8-bit builds, and a per-claim finishing map costs more than the 16 or 32 points it would replace (`knowledge/committed-matrix.md`).
- [x] **Split verification into transactions and bind the calls to each other.**
  - **The problem.** `FlockLift.verify` (432.2 M) and `FlockMatrix.verify` (326.1 M) each run as one call with the gas cap lifted, so "at least 46 transactions" is a lower bound, not a protocol.
  - **What to do.**
    - Make each call resumable across transactions that fit 2^24 gas, carrying its state by hash.
    - Have the lift contract commit its packed claims and statement digest in storage, so the matrix contract reads them instead of taking them as arguments.
  - **Done when** a whole verification runs as a measured sequence of capped transactions, and a matrix call on claims the lift contract did not produce is refused.
  - **Note.** The optimistic route (`knowledge/optimistic-verification.md`) already fits every transaction under the cap, but it does so by dispute, not by direct verification.
  - **Done** (2026-09-17): `verifier/src/staged/`, `knowledge/staged-verification.md`. A lift session and a matrix session run in 106 transactions, every one under 2^24 gas, for 889.16 M under `Fast` (781.19 M in 100 under `Slim`; `fixtures/evm-bench-2026-09-17-staged-*.summary.log`). The lift session records its statement digest with the hash of its claims, and `startMatrix` refuses any other claims (`crates/evm/tests/staged.rs`, validated by deletion).
- [x] **Bring the contracts under EIP-170.**
  - **The problem.** The runtime code of `FlockLift` is 94,320 bytes and that of `FlockMatrix` 94,197, against the 24,576-byte limit; the harness lifts the limit.
  - **What to do.** Most of the size is generated constants (`Constants.sol`: subspace table, φ₈ nodes, Ligerito schedules) and linked library code. Move the tables into separate data contracts read with `EXTCODECOPY`, and split the libraries into deployed contracts called with `DELEGATECALL`.
  - **Done when** every deployed contract is under the limit and the gas figures are re-measured with the limit enforced.
  - **Done** (2026-09-17): the staged verifier's nine contracts are 3,189 to 22,805 bytes. The Ligerito schedules became a byte table, the subspace table a data contract read with `EXTCODECOPY`, and the stages are split across contracts. The figures above were measured in an EVM enforcing both the size limit and the gas cap. The single-call contracts, now 53 KB, are kept as the reference and as the optimistic route's program, and are not deployed to run.
- [x] **Measure the `Slim` profile on the committed path.**
  - **The gap.** `POFSEED_LIGERITO_PROFILE=slim` was measured only with the row-walking discharge (lift contract 680.28 M against 830.28 M under `Fast`). It has not been run with the regular layout and the matrix contract, whose own opening is also profile-dependent.
  - **What to do.** Prove a 219-response lift under `Slim` into its own cache, run `evm-bench`, and add the row to `knowledge/performance-table.md`.
  - **Done when** the fixture exists and the table carries both profiles for the committed path.
  - **Done** (2026-09-17): 1,060.18 M gas against 1,265.90 M under `Fast`, at least 64 transactions (`fixtures/evm-bench-2026-09-17-committed-slim.summary.log`).

## Optimistic route

- [ ] **Widen the heaviest dispute step's margin.**
  - **The problem.** The heaviest step of the dispute game is `FlockMatrix` copying the 4,738-word matrix proof in one `CALLDATACOPY`. Resolved in a game it costs 14.84 M gas, 1.94 M under the transaction cap (`knowledge/optimistic-verification.md`).
  - **Why it matters.** A verifier that copied more calldata at once could not be disputed at all.
  - **What to do.** Split large copies across machine steps, or have the verifier read the proof in pieces.
  - **Done when** the heaviest resolved step has a comfortable margin, re-measured with the dispute simulator.
