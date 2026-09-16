# An Ethereum verifier for the Flock lift

Status: plan, 2026-09-16. This file becomes the record as the work lands.

The goal is a contract that verifies a lifted hardened-child proof on Ethereum L1, a gas measurement of that verification on the 219-response lift, and a first round of optimisations aimed at bringing it towards something deployable.

## What the EVM changes

Three facts decide the design before any code is written.

- **Field arithmetic is the unit of cost.** A GF(2^128) multiplication written in Yul, with a 4-bit window table and the loop unrolled, costs about 2,000 gas in Foundry (measured 2026-09-16, including a small loop overhead). The native verifier's core is 62,023,332 multiplications, so a straight port would cost on the order of 10^11 gas, and the opening's few hundred thousand multiplications on the order of 10^8–10^9.
- **The EVM has no hash midstate.** Flock's transcript is a running BLAKE3 (or SHA-256) state that is cloned and finalised at every challenge; neither `KECCAK256` nor the SHA-256 precompile can resume a state. The transcript therefore has to be a hash chain, which Flock's `Challenger` trait allows without forking Flock. Flock's Merkle hash can be SHA-256, which the EVM has as a precompile.
- **Transactions are capped at 2^24 gas** (EIP-7825, in force since the Fusaka upgrade), so anything larger is a multi-transaction protocol whatever its total.

## What the verifier computes

Per chunk: the statement binding, the zerocheck (a univariate skip over 64 points then 29 multilinear rounds), the lincheck replay with the matrix discharge, the published-word claim, three ring switches, and a Ligerito opening over GF(2^256) with stratified queries and SHA-256 Merkle paths.
Across chunks: the native Fiat-Shamir gate (Keccak-256, which the EVM has natively) and the journal checks.

The matrix discharge is where the cost is. Of the block's 8.69 M explicit rows, 6.38 M are the 1,600 link rows that set the input state of each of the 3,988 Keccak-f sub-blocks, and those repeat per sub-block up to a counter and a few selector bits, so they can be summed in closed form the way the Keccak sub-blocks already are. The rest — about 1.9 M rows of the two-party replay carrying some 40 M nonzeros, plus the sponge links — is the circuit description itself, and a verifier that evaluates it pays for it row by row.

The block also depends on the statement: the replay compiler folds constants, so the chain code shapes the rows. A contract can pin the rows of one statement by hash but cannot rebuild them for another.

## Plan

1. **An EVM-friendly transcript and Merkle hash in the lifter.** A Keccak-chained `Challenger` implemented in the lift crate, SHA-256 Merkle trees, and a flat proof encoding the contract parses. Measure what they cost the prover.
2. **The contract.** GF(2^128) and GF(2^256) arithmetic in Yul, the transcript, zerocheck, lincheck replay, ring switch, Ligerito, the published-word claim, the matrix discharge fed as hash-chained calldata, the Fiat-Shamir gate and the journal checks. Tested differentially against the Rust verifier through an in-process EVM (`revm`), which also lets the full-size discharge run without a file-size limit.
3. **The benchmark.** Gas per phase and in total for the 219-response hardened-child lift, and the number of 2^24-gas transactions that total implies.
4. **Optimisations**, each measured against the baseline: the multiplication kernel, removing field inversions from the verifier, closed-form link rows in the discharge, factorised `eq` tables, the Ligerito profile, and splitting the verification into transactions that each fit the cap.
5. **The record**: what the verifier costs, what each optimisation bought, and what separates the result from a deployable verifier.
