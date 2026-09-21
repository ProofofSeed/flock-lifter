# Design

How the verification of a ZKBoo proof of seed is laid out as a Flock statement, and why this layout rather than the alternatives Flock's machinery suggests.

## What must be proved

The lifted relation is the one the SP1 lifter proves by running `zkboo::verifier::verify` in a zkVM (catalogued formally in `~/git/zkboo/succinct-lifter/knowledge/lifted-relation.md`).
For each of the `N` responses `R_i = (c_i, s_i, s'_i, x_i, M_i, d_i)`:

- the two opened seeds are keyed into PRGs, `K = Keccak(TAG_PRG ‖ le64(32) ‖ s)`, whose tapes are blocks `Keccak(TAG_PRG ‖ K ‖ le64(counter))`;
- the two-party replay of the statement circuit consumes one tape word per slot per `bitand`/`carry` gate (and per `input` for a slot that draws its input share), recomputes the local AND messages, reads the remote ones from `M_i`, and absorbs the nonlinear outputs into one sponge per slot, `Keccak(TAG_VIEW ‖ le64(32) ‖ s ‖ stream)`;
- the two view digests and output shares, together with the unopened digest `d_i` and the third output share `y ⊕ o⁰ ⊕ o¹`, form `D_i`.

Globally, the challenge stream derived from `Keccak(TAG_CHALLENGE ‖ le64(|b|) ‖ b ‖ D_0 ‖ … ‖ D_{N−1})` must reproduce every `c_i`.

For the hardened-child statement on zkboo 1.3.0 (`statement-profile`, fingerprint `0x72936f44…`): 3,380 u64 `bitand`, 3,076 u64 `carry` and 13 u8 `bitand` gates, a 32-byte witness, and 413,288 AND-message bits per response.
That is 1,616 PRG blocks, 381 sponge blocks and one key derivation per slot, so **3,996 Keccak-f permutations per response**, against about 1.64 million two-party AND products.
The gates added since zkboo 1.2.1 are BIP-32's validity assertions (`zkboo-1.3.0-migration.md`).
The Keccak work is 99% of the Boolean relation.

## Flock's model, and what it rules out

Flock proves `z = (A·z) ∘ (B·z)` over GF(2), block-diagonal: one base block `(A₀, B₀)` of `2^k_log` bits repeated over `2^ν` rows, with several table types unioned into one committed polynomial.
Linear combinations inside a row are free; every committed bit costs.
Rows are related to one another, and to public words, only through the circuit layer's wiring argument, a grand-product permutation over *cells* — 128-bit words named in a type's IO schema.

The wiring argument is what rules out the obvious decompositions.
Its cell space has `2^(ν+c)` cells, `c` being the log of the number of schema words across all types, and the verifier evaluates the permutation's MLE in `O(2^(ν+c))`.
Splitting the lift into a Keccak table and a replay table joined by wires needs about thirteen thousand schema words per replay row (every tape block and every sponge block), so the cell space would be `2^34` or more for a verifier that is meant to be succinct.
A zkVM-style decomposition into per-gate rows fares no better.

## The response block

So each **response is one row**, and its block contains everything that response's verification computes: the replay, both key derivations, both PRG tapes and both view-commitment sponges.
Cross-links between the replay and its Keccak permutations are ordinary linear terms inside the row, which cost nothing.
Only `c_i`, the two view digests and the two output shares leave the row, through fifteen published IO words, so the cell space stays at `2^(ν+4)`.
The global Fiat-Shamir gate runs natively in the verifier over those public words and the unopened digests: it is a single Keccak sponge over about 60 kB, and it is what binds every challenge.

For the hardened child the block has `k_log = 28`.
It is tiled by 4,096 aligned sub-blocks of `2^16` bits: 3,996 hold one Keccak-f each, laid out as the retired Flock Keccak encoder did (input state, output state and the 24 χ outputs, with the intermediate states implicit), and the first 100 form the head, which holds the constant wire, the published words, the free inputs (seeds, the party-2 input share, `M_i`, the challenge bits) and the replay's products and materialised linear wires.

The replay's products and materialised wires are laid out regularly (`committed-matrix.md`).
Every product is committed, with a constant operand kept as a masked reference to the constant wire, and outputs are materialised at every bit of a gate or at none.
Each column kind of each gate limb has its own 64-bit word, so the rows of one gate differ only by a cyclic shift of their operands.
This costs 42% more replay rows, still inside the same `2^28` block and at no measurable proving time, and it is what lets the explicit rows be committed as three million entries instead of ninety million.

Challenge-dependence stays inside a fixed matrix:

- the challenge is one-hot `(h₀, h₁, h₂)`, published and checked natively;
- a slot receives the constant of `not` and `bitxor_const` exactly when `h₀` (slot 0) or `h₂` (slot 1) is set, which is linear;
- slot σ draws its input share from the tape exactly when `e₀ = h₀ ⊕ h₁` or `e₁ = h₀ ⊕ h₂` is set, and its gate tape is then shifted by one PRG block, which is absorbed by giving gate block `j` the counter `j + e_σ` — linear in `e_σ`, so tape positions are fixed;
- the input share itself is a 256-bit multiplexer between the tape and the free party-2 share.

## Lincheck without the base matrix

A `2^28`-column base matrix with every Keccak row substituted would hold billions of nonzeros, so the block implements `LincheckCircuit` structurally.
Head rows and the Keccak input-state rows, whose terms reach outside their sub-block, are stored sparsely.
The Keccak χ and output-pin rows are identical in every sub-block and are folded by the transpose recurrence of the retired Flock encoder, about a million field operations per sub-block and in parallel across them.

The prover needs that fold at every column, because its sumcheck binds the folded vector round by round.
The verifier does not: nothing in its replay reads the vector until the sumcheck's last equation, and by then the block's structure gives those 64 entries directly.
Because the sub-blocks are aligned, both `eq` tables factorise across a sub-block boundary, so the shared rows contribute one local fold times a sum of `eq` products over sub-block indices, and the explicit rows cost one multiplication per row and one per column slot each row touches.
`Program::comb_partial` evaluates that and `verify_lincheck_structured` uses it in place of Flock's `verify_with_grinding`, which would otherwise materialise two `2^28`-entry vectors and bind one of them 22 times.
It is eleven and a half times less arithmetic and eleven times less memory; `matrix-discharge.md` records the construction, the measurements and what is left.

The verifier has since stopped walking the explicit rows at all.
It evaluates the shared Keccak-f rows in rotation-invariant form: one kernel per lane, paired with a 64-entry table.
It hands each chunk's explicit-row part to one proof per lift, which shows those parts are the table-weighted sums of the statement's committed entry list (`committed-matrix.md`).

## Which Flock path proves the table

Flock has two ways to prove a Boolean table, and the response block's shape — very wide rows, very few of them — separates them by more than an order of magnitude.

The **union circuit path** (`crates/lift/src/chunk.rs`) is what Flock's circuit layer is built on: a registry of table types, the wiring argument for published words, and one merged opening.
It works, and it was the first path taken here, but its merged opening is built for tables with many rows and few word-columns.
Its block-first phase costs `(ring-switch claims) × 128 Frobenius powers × 2^(column bits)` field operations whatever the row count, so the `2^21` word-columns of a `2^28`-bit block spend 27.5 s there, and the merged sumcheck and multipoint weight passes another 49 s, on eight responses (`[open_merged]` trace).
With fewer live rows than capacity it falls off the rectangular fast path altogether and was killed at 124 GB on four responses.

The **single-table row-major path** (`crates/lift/src/chunk_rm.rs`) commits the rows contiguously and opens the zerocheck's and lincheck's two claims with an ordinary ring-switch and Ligerito batch opening.
On the same eight responses it proves in 3.18 s against 54 s, and the opening itself is 0.09 s (`fixtures/chunk-8-row-major-2026-09-14.summary.log`, `fixtures/chunk-8-union-2026-09-14.summary.log`); a later side-by-side run peaked at 21.5 GB against 32.4 GB (`fixtures/chunk-8-union-vs-row-major-2026-09-17.summary.log`).
It has no circuit layer, so the published words are bound by a third claim appended to the same batched opening: the words are absorbed into the transcript before the commitment, and the claim evaluates the committed witness on the published-word subcube (word-columns 16 to 31 of every row, which is why they sit there) at a point sampled after it, with a value the verifier computes from the words.
Padding rows repeat the last live block, because this path's constant-wire pin must hold in every row.

Flock's single-table core verifier refuses any statement whose `C₀` is not a materialised identity matrix, since its c-claim is a direct witness claim only in circuit form.
The block is in circuit form by construction, and a materialised identity of `2^28` rows would cost the verifier gigabytes, so `chunk_rm.rs` replays the same core — statement binding, zerocheck, lincheck, claim reconstruction — through Flock's public functions without that one check.
Its lincheck is this lifter's own replay of Flock's, which walks the same transcript and refuses the same shapes but discharges the matrix claims structurally; the two accept each other's proofs byte for byte.

## What a verified lift establishes

The verifier (`crates/lift/src/lift.rs`) holds the statement — chain code, index, expected output, binding — and builds the response block itself from the public-only circuit, so a proof never selects the constraint system it is checked against.
It then checks, in order:

1. the lifted proof's parts agree in length, and its chunk count matches its response count and chunk size;
2. every chunk's Flock proof, under a transcript domain that binds the statement digest (circuit fingerprint, statement fields, response count, chunk size) and the chunk's position, against the words the chunk's blocks publish;
3. that every published challenge word is one-hot;
4. the matrix proof, against the statement's pinned entry commitment, for the explicit-row part of every chunk's matrix claim;
5. the global Fiat-Shamir gate, natively: the challenge transcript over the binding and, per response in absolute party order, the two published view digests with their output shares and the unopened digest with the third share `y ⊕ o⁰ ⊕ o¹`, must derive exactly the published challenges.

A chunk proof attests, under Flock's assumptions, knowledge of rows satisfying the block's relation whose published words are the ones given.
A row satisfies the relation exactly when some seeds, AND messages and party-2 input share replay the circuit, under the published challenge and with Keccak-256 PRG tapes and view commitments, to the published digests and output shares.
With the gate, the responses together form an accepting ZKBoo transcript for the statement, which is what the SP1 lifter's guest establishes by running `zkboo::verifier::verify`.
The journal is then built from the verifier's own values and put through the same `check_journal` gate, assertion word and repetition count included.

The acceptance run (`acceptance rejects`) names the refuser of every case, and the checks that nothing else backs were validated by deletion (`fixtures/deletion-validation-2026-09-14.summary.log`, `fixtures/deletion-validation-2026-09-15.summary.log`).
With the Fiat-Shamir comparison removed, a proof with one AND-message bit flipped lifts and verifies; with the published-word claim removed from the opening, a chunk proved over published words its witness does not carry verifies; and with the lincheck's final comparison removed, a chunk whose matrix evaluation is deliberately wrong verifies.
Each of the matrix proof's three checks was validated the same way against a forging prover (`fixtures/deletion-validation-2026-09-16-committed-matrix.summary.log`).
The other refusals — a tampered published word, a swapped chunk, another statement — are enforced by the transcript binding before either check is reached.

That the compiled block means what the replay means is established by test, not by proof: `crates/block/tests/block.rs` checks every published word against ZKBoo's own replay for all three challenges, on a circuit that exercises every gate kind and on the hardened child at full size, checks the structured lincheck fold against the witness it folds, and checks the structured matrix discharge against the dense fold it replaces.
This is the lift-fidelity gap the SP1 lifter does not have, since its guest is the verifier itself.

The assumptions stack as follows.
ZKBoo's soundness at 219 responses is the classical-128 figure in the forgery-work-ratio sense, with the caveat the SP1 lifter records.
Flock's Ligerito `Fast` profile targets 128-bit component security (`docs/128-bit-grinding-audit.md` in Flock), on proximity-gap results in the proven regime and SHA-256 for its Merkle commitments; the lifter's transcript is a Keccak-256 hash chain, so that an EVM contract can replay it (`evm-verifier.md`).
The composition of an in-circuit Keccak with a random-oracle Fiat-Shamir argument is heuristic exactly where every hash-based recursion is.
There is no pairing anywhere, so the BN254 ceiling of about 100 bits that caps the SP1 lifter does not apply; whether the lift is post-quantum depends on Flock's grinding being re-accounted under Grover, which is not established here, and on lifting 438 responses rather than 219.
Flock describes itself as a research prototype not for production use, and this lifter inherits that.

## Scope limits

The Ethereum-address statement does not fit this design on this machine.
Its responses carry about 23.5 million AND-message bits, so its block would need `k_log = 34`, where the dense lincheck fold is `2^34` field elements or about 275 GB.
The verifier no longer builds that vector, and its structured discharge would want about 8.6 GB at `k_log = 34`; the **prover** still builds it, because its sumcheck binds the folded vector round by round.
So what blocks the elephant is the prover's fold, not the verifier's, and the compiler's inability to handle inputs allocated after the first AND gate.

An on-chain verifier exists and is measured (`evm-verifier.md`, `committed-matrix.md`).
With the regular layout and the committed matrix, verifying the 219-response lift in EVM contracts costs 1.27 billion gas, at least 76 transactions at the 2^24-gas cap, and 758 million, at least 46, with Ligerito's final-level residuals evaluated in assembly.
The row-walking discharge it replaced cost 158 billion.
Most of what remains is Ligerito's final-level verification, three openings of a few hundred million gas each, which matches the estimate recorded here on 2026-09-15 of 100–400 M gas per chunk for the opening alone.
That is still far from a single transaction. Split into transactions under mainnet's limits and bound to each other on chain, it takes 889 million gas in 106 transactions (`staged-verification.md`).

To serve the contract, the lifter's transcript is a Keccak-256 hash chain and its Merkle trees are SHA-256, both of which the EVM has natively.
The published words stay linear in the response count (52.6 kB at 219) unless the Fiat-Shamir gate moves into the circuit.
`verifier-routes.md` costs the four routes considered: a committed matrix and a shift-regular layout, both now built; wrapping in a succinct proof, which is not pursued because it would give up what this lifter is for; and optimistic verification, which is being investigated separately.
A search on 2026-09-15 found no published on-chain verifier for Flock or Ligerito to calibrate against.

## Batching and Ligerito

One Flock proof covers up to `2^ν` responses.
Ligerito security configurations are registered for committed sizes up to `m = 35`, which holds 128 responses of `2^28` bits, so a 219-response lift is two proofs (128 and 91, the latter padded to 128 rows) sharing one native Fiat-Shamir gate.
