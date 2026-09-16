# An Ethereum verifier for the Flock lift

Status: record, 2026-09-16.
The Flock lift can be verified by EVM contracts, and the verification of the 219-response hardened-child lift is metered phase by phase.
It costs **158.3 billion gas**, at least **9,438 transactions** at the 2^24-gas cap.
That is a quarter of the first working version's figure, and still about **564,000×** what the SP1 lifter's Groth16 verification costs on L1 (280,590 gas).
The structural reason is below, together with what would have to change for a Flock verifier to be deployable.

## What the EVM changes

Three facts shaped the design before any code was written.

- **Field arithmetic is the unit of cost.** A GF(2^128) multiplication in Yul, with a 4-bit window table and the loop unrolled, costs about 1,800 gas, and a squaring about 440. The native verifier's matrix discharge is 62 M multiplications, so a straight port costs on the order of 10^11 gas.
- **The EVM has no hash midstate.** Flock's transcript is a running hash state cloned and finalised at every challenge, and neither `KECCAK256` nor the SHA-256 precompile can resume a state. The lifter therefore uses a hash-chained transcript, which Flock's `Challenger` trait allows without forking Flock, and SHA-256 Merkle trees, which the EVM has as a precompile.
- **Transactions are capped at 2^24 gas** (EIP-7825), so anything larger is a multi-transaction protocol whatever its total.

## What was built

- **The transcript and Merkle hash in the lifter.** `crates/lift/src/transcript.rs` is a Keccak-256 hash-chain `Challenger`: absorbing replaces the state `h` with `keccak(h ‖ bytes)`, output block `j` is `keccak(h ‖ u64be(j))`, and grinding checks the leading zero bits of `keccak(h ‖ u64be(nonce) ‖ u64be(bits))`. Flock's framing headers are kept, and field elements are absorbed big-endian. Chunk proofs use SHA-256 Merkle trees. Neither change moved proof size or prove time measurably.
- **`crates/evm`** (`pofseed-flock-lift-evm`):
  - a calldata encoder that lays a lift out in the order the contract consumes it;
  - a Rust **mirror** verifier over that calldata, checked against the lifter's own verifier and against tampered bytes, which is the contract's oracle;
  - an in-process EVM harness on `revm` under Osaka rules, with the gas cap, block gas limit, code-size limit and memory limit lifted so the full-size phases run as single calls;
  - the discharge stream generator (`stream.rs`), which checks every row a family record stands for against the block;
  - the binaries `evm-bench` (the benchmark), `evm-constants` (generates `verifier/src/Constants.sol`) and `row-shapes` (how regular the block's rows are).
- **`verifier/`**, a Foundry project compiled with legacy codegen (via-IR could not resolve its stack depth):
  - `FlockLift` is deployed per statement and pins the circuit fingerprint, chain code, index, minimum response count and commitment profile. It verifies every chunk (zerocheck, lincheck up to its matrix claim, published-word claim, ring switches, Ligerito over GF(2^256)), runs the ZKBoo Fiat-Shamir gate and the assertion word, and returns the packed matrix claims.
  - `FlockDischarge` is deployed per statement and pins the hash chain of the block's explicit-row stream. It evaluates the matrix claims in three phases: `keccakPart` (the 3,988 Keccak-f sub-blocks through one shared fold), `rows` (one call per stream segment) and `finish`.
  - `GF2`, `Transcript`, `Piop`, `Opening`, `Tensor`, `Tables` and `FiatShamir` are the libraries behind them. `FlockVerifier` is a single-chunk test contract, and `probes/` holds test entry points for the field and the gate.
- **Tests** (`cargo test --release -p pofseed-flock-lift-evm`, all passing):
  - field operations against Flock's;
  - the mirror against the lifter's verifier, with tampering;
  - the chunk contract against the mirror;
  - the lift contract on a genuine lift;
  - the gate against nine forgeries;
  - the discharge contract against the native discharge on a toy block, with refused negatives.

The block depends on the statement, because the replay compiler folds the chain code into the rows, so both contracts are per statement.

## What it costs

Measured by `evm-bench 219` on 2026-09-16, gas as revm reports it per call, calldata priced at the standard 4/16 per byte plus 21,000 per call.
Fixtures: `fixtures/evm-bench-2026-09-16-baseline.summary.log` (first working version), `…-optimised.summary.log` and `…-optimised-slim.summary.log`.
The middle column comes from a run at commit `ab01823` whose log was not kept as a fixture.

| gas (millions)                    |    baseline |   `ab01823` | optimised, Fast | optimised, Slim |
| --------------------------------- | ----------: | ----------: | --------------: | --------------: |
| lift contract, both chunks + gate |    1,138.56 |      900.00 |          830.28 |          680.28 |
| discharge, Keccak sub-blocks      |    1,413.01 |    1,037.24 |        1,037.24 |        1,037.24 |
| discharge, stream execution       |     665,599 |     332,867 |         153,311 |         153,311 |
| — of it, per-call table setup     |           — |     109,088 |           1,784 |           1,784 |
| discharge, stream calldata        |       3,921 |       3,112 |           3,112 |           3,112 |
| discharge, final check            |        0.64 |       50.95 |           50.95 |           50.95 |
| **verification in all**           | **672,073** | **337,968** |     **158,342** |     **158,192** |
| transactions under 2^24, at least |      40,059 |      20,145 |           9,438 |           9,429 |

Chunk 1 of the lift contract (chunk 2 is within 3% on every phase but the published-word claim, which it carries fewer responses for):

| phase                      | Fast (M gas) | Slim (M gas) | baseline, Fast (M gas) |
| -------------------------- | -----------: | -----------: | ---------------------: |
| published words            |         1.52 |         1.52 |                   1.52 |
| zerocheck                  |         1.44 |         1.44 |                   1.44 |
| lincheck                   |         0.92 |         0.92 |                   0.92 |
| published-word claim       |        13.81 |        13.81 |                  13.81 |
| ring switches              |         6.35 |         6.35 |                   6.34 |
| Ligerito level 0           |        47.07 |        23.59 |                  47.08 |
| Ligerito levels 1–5, final |        15.89 |        13.99 |                  15.89 |
| ring-switch residual       |       186.76 |       186.72 |                 274.28 |
| out-of-domain residual     |         4.69 |         4.69 |                   4.73 |
| consistency residual       |       125.64 |        79.42 |                 188.61 |

The lift contract is dominated by the two residuals of the opening's last level, which evaluate multilinear objects over the committed polynomial's `m = 35` variables.
The Fiat-Shamir gate over all 219 responses is 2.05 M.
Deployment costs 18.83 M gas for `FlockLift`.

## What each optimisation bought

- **Table-driven tensor algebra** for the ring-switch residual. The rows of the "multiply by q" matrix follow a linear recurrence, so 8-bit combination tables built by doubling replace per-bit transposes. Per chunk: 274–282 M → 187–189 M.
- **A precomputed subspace-polynomial table** (`SUBSPACE[k][b]`), so each stratified query's subspace values are XORs. In a later round, the stratified queries are folded into one weight vector before a single evaluation. Per chunk: 189 M → 160 M → 126 M.
- **The Slim profile** (rate 1/4) halves the level-0 opening and cuts the consistency residual to 79 M, for a third off the proof and about a fifth more proving. The contract pins the profile per statement.
- **Discharge, closed-form families.** The 1,600 PRG link rows of each Keccak sub-block, the sponge links and the identity words are summed in closed form from per-claim tables, instead of row by row.
- **Discharge, per-claim 8-bit multiplication tables** for the 64 slot weights and for α, and head, tape and sponge-input weight tables. Every row is then accumulated straight into one scalar per claim.
- **Discharge, hashing a segment in 32 KiB pieces** instead of copying it whole. Memory expansion is quadratic, and copying the 238 MB stream cost 107 B of the 109 B per-call overhead. That overhead is now 1.78 B.
- **Discharge, the row loop in Yul.** It removes Solidity's call overhead from a loop over 2.72 M row records and 53.5 M column references per claim: 224 B → 152 B.
  🪤 The first version of this loop allocated a four-word constant array inside the per-row function, and the free pointer's growth made it **cost 415 B**, nearly twice what it replaced. A memory allocation inside a hot loop is quadratic in the EVM.

Altogether: **4.24×** on the whole verification, 1.37× on the lift contract (1.67× with Slim), and 4.39× on the stream's row execution.

## What the measurement does not cover

- **It is not split into transactions.** Each phase ran as one call with the cap lifted, so the transaction count is a lower bound. Three things stop a straightforward split:
  - the discharge builds its per-claim tables in every `rows` call, and that setup alone is about 890 M gas per claim, far above the cap;
  - the lift contract is 830 M gas in one call;
  - nothing yet carries a verification's state across transactions.
- **The calls are not bound to each other on chain.** In the benchmark, the harness passes the lift contract's claims to the discharge. A deployment must store or hash-commit them between calls, and has to price that in.
- **`FlockLift`'s runtime code is 87,321 bytes**, over EIP-170's 24,576-byte limit, which the harness lifts. Most of it is generated constant tables. A deployment must split the contract. `FlockDischarge` is 22,586 bytes and fits.
- **Security.** Soundness is Flock's under the Fast (or Slim) profile, with the transcript's hash chain modelled as a random oracle. The lift-fidelity gap of `design.md` applies unchanged.

## Why this is not close to deployable, and what would be

The discharge is 99% of the cost, and it is not an implementation artefact that more tuning removes.
The block's explicit rows are the two-party replay itself: about 1.9 M rows carrying 49 M nonzeros, which `row-shapes` shows are not shift-regular.
Only 414 k head rows fall into periodic runs.
SHA-512's rotations wrap modulo 64, and many rows carry several product columns.
After the closed-form families, the stream still holds 2,718,991 row records carrying 53,484,554 column references (`row-shapes`).
Each reference needs, per claim, a calldata read, a weight lookup and a slot update, a few hundred gas at the very least.
So **any EVM evaluation of these rows costs tens of billions of gas**, thousands of transactions, however it is written; the current figure, about 1,420 gas per reference per claim with the per-row work included, is within a small factor of that floor.
Even the lift contract alone, without the discharge, is about fifty transactions.

Getting the matrix off chain changes the order of magnitude. None of these routes is measured:

- **Committed (holographic) matrix evaluation.** The block is committed once, at deployment, and the prover proves the matrix claims against that commitment, so the verifier checks an opening instead of walking the rows. Flock has no such commitment. Its `matrix_fold` accumulation, which was costed natively on 2026-09-15 and declined (`matrix-discharge.md`), folds many claims into one but still ends in one `O(nnz)` discharge, so on its own it does not help a contract. A commitment would leave a second opening of roughly the lift contract's size, by analogy with the opening measured here: hundreds of millions of gas, tens of transactions.
- **A uniform block layout.** A replay whose rows repeat by shift would let the discharge be summed in closed form, as the PRG and sponge families already are. That means recompiling the circuit into a regular layout, at a prover cost not yet estimated.
- **Wrapping.** Prove the native Flock verifier (0.06 s, 62 M field multiplications at 219 responses) inside a system with a cheap L1 verifier, as the SP1 lifter does for the ZKBoo verifier at 280,590 gas. The on-chain cost is then that system's, and the question moves to the wrapping prover, which is not measured. Flock's own notes add that a Flock proof of this verifier would be nnz-sized too, so recursion within Flock needs the holographic step first.
- **Optimistic verification.** Accept the lift unless challenged, and settle a challenge by bisection over the discharge stream. That brings the on-chain cost of an honest lift near zero and the cost of a dispute to a few segments, at the price of a challenge window. It is not a verifier in the sense of this record.

The lift contract's own cost is also far from viable: 680–830 M gas, dominated by the Ligerito residuals over `m = 35` variables.
Every route above keeps it, except wrapping.
