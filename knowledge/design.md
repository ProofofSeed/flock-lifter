# Design

How the verification of a ZKBoo proof of seed is laid out as a Flock statement, and why this layout rather than the alternatives Flock's machinery suggests.

## What must be proved

The lifted relation is the one the SP1 lifter proves by running `zkboo::verifier::verify` in a zkVM (catalogued formally in `~/git/zkboo/succinct-lifter/knowledge/lifted-relation.md`).
For each of the `N` responses `R_i = (c_i, s_i, s'_i, x_i, M_i, d_i)`:

- the two opened seeds are keyed into PRGs, `K = Keccak(TAG_PRG ‖ le64(32) ‖ s)`, whose tapes are blocks `Keccak(TAG_PRG ‖ K ‖ le64(counter))`;
- the two-party replay of the statement circuit consumes one tape word per slot per `bitand`/`carry` gate (and per `input` for a slot that draws its input share), recomputes the local AND messages, reads the remote ones from `M_i`, and absorbs the nonlinear outputs into one sponge per slot, `Keccak(TAG_VIEW ‖ le64(32) ‖ s ‖ stream)`;
- the two view digests and output shares, together with the unopened digest `d_i` and the third output share `y ⊕ o⁰ ⊕ o¹`, form `D_i`.

Globally, the challenge stream derived from `Keccak(TAG_CHALLENGE ‖ le64(|b|) ‖ b ‖ D_0 ‖ … ‖ D_{N−1})` must reproduce every `c_i`.

For the hardened-child statement (`statement-profile`): 3,376 u64 `bitand`, 3,068 u64 `carry` and 10 u8 `bitand` gates, a 32-byte witness, and 412,496 AND-message bits per response.
That is 1,613 PRG blocks, 380 sponge blocks and one key derivation per slot, so **3,988 Keccak-f permutations per response**, against about 1.65 million two-party AND products.
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
It is tiled by 4,096 aligned sub-blocks of `2^16` bits: 3,988 hold one Keccak-f each, laid out as the retired Flock Keccak encoder did (input state, output state and the 24 χ outputs, with the intermediate states implicit), and the first 108 form the head, which holds the constant wire, the published words, the free inputs (seeds, the party-2 input share, `M_i`, the challenge bits) and the replay's products and materialised linear wires.

Challenge-dependence stays inside a fixed matrix:

- the challenge is one-hot `(h₀, h₁, h₂)`, published and checked natively;
- a slot receives the constant of `not` and `bitxor_const` exactly when `h₀` (slot 0) or `h₂` (slot 1) is set, which is linear;
- slot σ draws its input share from the tape exactly when `e₀ = h₀ ⊕ h₁` or `e₁ = h₀ ⊕ h₂` is set, and its gate tape is then shifted by one PRG block, which is absorbed by giving gate block `j` the counter `j + e_σ` — linear in `e_σ`, so tape positions are fixed;
- the input share itself is a 256-bit multiplexer between the tape and the free party-2 share.

## Lincheck without the base matrix

A `2^28`-column base matrix with every Keccak row substituted would hold billions of nonzeros, so the block implements `LincheckCircuit` structurally.
Head rows and the Keccak input-state rows, whose terms reach outside their sub-block, are stored sparsely.
The Keccak χ and output-pin rows are identical in every sub-block and are folded by the transpose recurrence of the retired Flock encoder, about a million field operations per sub-block and in parallel across them.

Because the sub-blocks are aligned, the verifier's matrix evaluation factorises: the shared rows contribute one local evaluation times a sum of `eq` products over sub-block indices, and only the sparse rows are paid per nonzero.

## Which Flock path proves the table

Flock has two ways to prove a Boolean table, and the response block's shape — very wide rows, very few of them — separates them by more than an order of magnitude.

The **union circuit path** (`crates/lift/src/chunk.rs`) is what Flock's circuit layer is built on: a registry of table types, the wiring argument for published words, and one merged opening.
It works, and it was the first path taken here, but its merged opening is built for tables with many rows and few word-columns.
Its block-first phase costs `(ring-switch claims) × 128 Frobenius powers × 2^(column bits)` field operations whatever the row count, so the `2^21` word-columns of a `2^28`-bit block spend 27.5 s there, and the merged sumcheck and multipoint weight passes another 49 s, on eight responses (`[open_merged]` trace).
With fewer live rows than capacity it falls off the rectangular fast path altogether and was killed at 124 GB on four responses.

The **single-table row-major path** (`crates/lift/src/chunk_rm.rs`) commits the rows contiguously and opens the zerocheck's and lincheck's two claims with an ordinary ring-switch and Ligerito batch opening.
On the same eight responses it proves in 3.18 s against 54 s, in 21.5 GB against 32 GB, and the opening itself is 0.09 s.
It has no circuit layer, so the published words are bound by a third claim appended to the same batched opening: the words are absorbed into the transcript before the commitment, and the claim evaluates the committed witness on the published-word subcube (word-columns 16 to 31 of every row, which is why they sit there) at a point sampled after it, with a value the verifier computes from the words.
Padding rows repeat the last live block, because this path's constant-wire pin must hold in every row.

Flock's single-table core verifier refuses any statement whose `C₀` is not a materialised identity matrix, since its c-claim is a direct witness claim only in circuit form.
The block is in circuit form by construction, and a materialised identity of `2^28` rows would cost the verifier gigabytes, so `chunk_rm.rs` replays the same core — statement binding, zerocheck, lincheck, claim reconstruction — through Flock's public functions without that one check.

## Batching and Ligerito

One Flock proof covers up to `2^ν` responses.
Ligerito security configurations are registered for committed sizes up to `m = 35`, which holds 128 responses of `2^28` bits, so a 219-response lift is two proofs (128 and 91, the latter padded to 128 rows) sharing one native Fiat-Shamir gate.
