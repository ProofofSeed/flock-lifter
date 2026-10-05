// SPDX-License-Identifier: LGPL-3.0-or-later

//! The response block as a program: its explicit rows, the order in which rows and Keccak-f
//! sub-blocks are evaluated, the witness of one response, and the structured lincheck fold.

use crate::{
    form::{CONST, Form},
    keccak::{self, Lanes, SUB_BITS, SUB_LOG},
    layout::{DIGEST_BITS, Geometry, RATE_BYTES, SEED_BITS, StatementShape, SubKind, VIEW_PREFIX_BYTES, h_col},
    replay::{self, Replay},
};
use flock_prover::{
    field::F128,
    lincheck::{LincheckCircuit, build_eq_table},
    matrix_fold::FoldMatrix,
};
use pofseed_flock_lift_statement::S;
use rayon::prelude::*;
use zkboo::{
    circuit::Circuit,
    crypto::{TAG_PRG, TAG_VIEW_COMMITMENT},
    prover::proof::Response,
    word::Words,
};

/// One step of block evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// Rows whose columns are free inputs, set from the response.
    Free(u32, u32),
    /// Rows evaluated in order.
    Rows(u32, u32),
    /// A Keccak-f sub-block whose input state its link rows have just set.
    Keccak(u32),
}

/// Why a response cannot be laid into the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
    /// The response's AND messages do not have the statement's shape.
    AndMsgShape,
    /// The response's party-2 input share is present when it must be absent, absent when it
    /// must be present, or of the wrong shape.
    InputShareShape,
}

/// Explicit rows one thread takes at a time in the structured discharge.
const EXPLICIT_CHUNK: usize = 1 << 16;

#[derive(Default)]
struct RowsBuilder {
    cols: Vec<u32>,
    a_ptr: Vec<u32>,
    a_idx: Vec<u32>,
    b_ptr: Vec<u32>,
    b_idx: Vec<u32>,
}

impl RowsBuilder {
    fn push(&mut self, col: u32, a: &Form, b: &Form) {
        if self.a_ptr.is_empty() {
            self.a_ptr.push(0);
            self.b_ptr.push(0);
        }
        self.cols.push(col);
        self.a_idx.extend_from_slice(a.cols());
        self.a_ptr.push(self.a_idx.len() as u32);
        self.b_idx.extend_from_slice(b.cols());
        self.b_ptr.push(self.b_idx.len() as u32);
    }

    fn len(&self) -> u32 {
        return self.cols.len() as u32;
    }
}

fn bytes_bits(bytes: &[u8], p: usize) -> bool {
    return (bytes[p / 8] >> (p % 8)) & 1 == 1;
}

fn counts(words: &Words) -> [usize; 3] {
    return [
        words.as_vec::<u8>().len(),
        words.as_vec::<u32>().len(),
        words.as_vec::<u64>().len(),
    ];
}

/// The response block of a statement circuit.
pub struct Program {
    geometry: Geometry,
    replay_products: usize,
    replay_materialised: usize,
    rows: RowsBuilder,
    schedule: Vec<Step>,
}

impl StatementShape {
    /// The shape of a circuit, measured by ZKBoo's profiling backend.
    pub fn of<C: Circuit>(circuit: &C) -> Self {
        let data = zkboo_profiling::profile(circuit);
        let g = data.gate_counts();
        let get = |s: &zkboo::word::Shape| [*s.as_value::<u8>(), *s.as_value::<u32>(), *s.as_value::<u64>()];
        let (and, carry) = (get(&g.bitand), get(&g.carry));
        return Self {
            inputs: get(&g.input),
            and_msgs: [0, 1, 2].map(|t| and[t] + carry[t]),
            outputs: get(&g.output),
        };
    }
}

impl Program {
    /// Builds the block of `circuit`, laid out regularly: every gate word bit-aligned, every bit
    /// laid out alike.
    pub fn new<C: Circuit>(circuit: &C) -> Self {
        return Self::build(circuit, replay::compile_regular_fitting);
    }

    /// Builds the block of `circuit` with the compact layout, which skips constant products and
    /// allocates columns in evaluation order.
    pub fn compact<C: Circuit>(circuit: &C) -> Self {
        return Self::build(circuit, replay::compile);
    }

    fn build<C: Circuit>(circuit: &C, compile: fn(&C, &Geometry) -> Result<Replay, usize>) -> Self {
        let shape = StatementShape::of(circuit);
        let mut k_log = SUB_LOG + 1;
        let mut head_bits = 0;
        let (geometry, replay) = loop {
            let Some(geometry) = Geometry::new(shape.clone(), k_log, head_bits) else {
                k_log += 1;
                continue;
            };
            match compile(circuit, &geometry) {
                Ok(replay) => break (geometry, replay),
                Err(needed) => head_bits = needed,
            }
        };
        return Self::assemble(geometry, replay);
    }

    fn assemble(geometry: Geometry, replay: Replay) -> Self {
        let g = &geometry;
        let shape = g.shape().clone();
        let mut rows = RowsBuilder::default();
        let mut schedule = Vec::new();
        let konst = Form::col(CONST);
        let start = rows.len();
        rows.push(CONST, &konst, &konst);
        for p in 0..3 {
            rows.push(h_col(p), &Form::col(h_col(p)), &konst);
        }
        for s in 0..2 {
            for p in 0..SEED_BITS {
                rows.push(g.seed_col(s, p), &Form::col(g.seed_col(s, p)), &konst);
            }
        }
        for p in 0..shape.input_bits() {
            rows.push(g.x_col(p), &Form::col(g.x_col(p)), &konst);
        }
        for p in 0..shape.and_msg_bits() {
            rows.push(g.m_col(p), &Form::col(g.m_col(p)), &konst);
        }
        schedule.push(Step::Free(start, rows.len()));
        let selectors = [
            Form::from_cols(vec![h_col(0), h_col(1)]),
            Form::from_cols(vec![h_col(0), h_col(2)]),
        ];
        let links = |rows: &mut RowsBuilder, schedule: &mut Vec<Step>, s: usize, kind: SubKind, forms: Vec<Form>| {
            let start = rows.len();
            for (p, f) in forms.iter().enumerate() {
                rows.push(g.state0_col(s, kind, p), f, &Form::col(CONST));
            }
            schedule.push(Step::Rows(start, rows.len()));
            schedule.push(Step::Keccak(g.sub_index(s, kind) as u32));
        };
        let padded = |bits: &mut Vec<Form>, len_bits: usize| {
            bits.resize(keccak::STATE_BITS, Form::zero());
            bits[len_bits].xor_assign(&Form::col(CONST));
            bits[RATE_BYTES * 8 - 1].xor_assign(&Form::col(CONST));
        };
        for s in 0..2 {
            let mut prefix = TAG_PRG.to_vec();
            prefix.extend_from_slice(&(SEED_BITS as u64 / 8).to_le_bytes());
            let mut bits: Vec<Form> = (0..prefix.len() * 8).map(|p| Form::constant(bytes_bits(&prefix, p))).collect();
            bits.extend((0..SEED_BITS).map(|p| Form::col(g.seed_col(s, p))));
            let len = bits.len();
            padded(&mut bits, len);
            links(&mut rows, &mut schedule, s, SubKind::Key, bits);
        }
        for s in 0..2 {
            for i in 0..g.prg_blocks() {
                let mut bits: Vec<Form> = (0..TAG_PRG.len() * 8).map(|p| Form::constant(bytes_bits(TAG_PRG, p))).collect();
                bits.extend((0..DIGEST_BITS).map(|p| Form::col(g.state24_col(s, SubKind::Key, p))));
                for q in 0..64 {
                    let bit = |c: usize| (c >> q) & 1 == 1;
                    let f = if i < g.in_blocks() {
                        Form::constant(bit(i))
                    } else {
                        let j = i - g.in_blocks();
                        let mut f = Form::constant(bit(j));
                        if bit(j) != bit(j + g.in_blocks()) {
                            f.xor_assign(&selectors[s]);
                        }
                        f
                    };
                    bits.push(f);
                }
                let len = bits.len();
                padded(&mut bits, len);
                links(&mut rows, &mut schedule, s, SubKind::Prg(i), bits);
            }
        }
        let start = rows.len();
        for row in &replay.rows {
            rows.push(row.col, &row.a, &row.b);
        }
        for s in 0..2 {
            for (p, f) in replay.outputs[s].iter().enumerate() {
                rows.push(g.out_col(s, p), f, &konst);
            }
        }
        schedule.push(Step::Rows(start, rows.len()));
        let preimage_bits = VIEW_PREFIX_BYTES * 8 + shape.stream_bits();
        for s in 0..2 {
            let mut prefix = TAG_VIEW_COMMITMENT.to_vec();
            prefix.extend_from_slice(&(SEED_BITS as u64 / 8).to_le_bytes());
            let mut preimage: Vec<Form> = (0..prefix.len() * 8).map(|p| Form::constant(bytes_bits(&prefix, p))).collect();
            preimage.extend((0..SEED_BITS).map(|p| Form::col(g.seed_col(s, p))));
            preimage.extend(replay.streams[s].iter().cloned());
            assert_eq!(preimage.len(), preimage_bits);
            preimage.push(Form::constant(true));
            preimage.resize(g.sponge_blocks() * RATE_BYTES * 8, Form::zero());
            preimage[g.sponge_blocks() * RATE_BYTES * 8 - 1].xor_assign(&konst);
            for b in 0..g.sponge_blocks() {
                let forms: Vec<Form> = (0..keccak::STATE_BITS)
                    .map(|p| {
                        let mut f = if p < RATE_BYTES * 8 {
                            preimage[b * RATE_BYTES * 8 + p].clone()
                        } else {
                            Form::zero()
                        };
                        if b > 0 {
                            f.xor_assign(&Form::col(g.state24_col(s, SubKind::Sponge(b - 1), p)));
                        }
                        f
                    })
                    .collect();
                links(&mut rows, &mut schedule, s, SubKind::Sponge(b), forms);
            }
        }
        let start = rows.len();
        for s in 0..2 {
            let last = SubKind::Sponge(g.sponge_blocks() - 1);
            for p in 0..DIGEST_BITS {
                rows.push(g.digest_col(s, p), &Form::col(g.state24_col(s, last, p)), &konst);
            }
        }
        schedule.push(Step::Rows(start, rows.len()));
        return Self {
            geometry,
            replay_products: replay.products,
            replay_materialised: replay.materialised,
            rows,
            schedule,
        };
    }

    /// The block geometry.
    pub fn geometry(&self) -> &Geometry {
        return &self.geometry;
    }

    /// Committed two-party AND products in the replay.
    pub fn replay_products(&self) -> usize {
        return self.replay_products;
    }

    /// Materialised linear forms in the replay.
    pub fn replay_materialised(&self) -> usize {
        return self.replay_materialised;
    }

    /// Number of explicit rows.
    pub fn explicit_rows(&self) -> usize {
        return self.rows.cols.len();
    }

    /// Nonzeros of the explicit rows, A side then B side.
    pub fn explicit_nnz(&self) -> (usize, usize) {
        return (self.rows.a_idx.len(), self.rows.b_idx.len());
    }

    /// Block width in bits.
    pub fn block_bits(&self) -> usize {
        return 1 << self.geometry.k_log();
    }

    /// Explicit row `r`: the column it defines, then its A-side and B-side columns.
    pub fn explicit_row(&self, r: usize) -> (u32, &[u32], &[u32]) {
        return (self.rows.cols[r], self.row_a(r), self.row_b(r));
    }

    fn row_a(&self, r: usize) -> &[u32] {
        return &self.rows.a_idx[self.rows.a_ptr[r] as usize..self.rows.a_ptr[r + 1] as usize];
    }

    fn row_b(&self, r: usize) -> &[u32] {
        return &self.rows.b_idx[self.rows.b_ptr[r] as usize..self.rows.b_ptr[r + 1] as usize];
    }

    /// Checks that a response has the statement's shape: AND messages of the statement's shape,
    /// and a party-2 input share of the statement's shape exactly when the challenge opens party 2.
    pub fn check_response(&self, response: &Response<S, S>) -> Result<(), WitnessError> {
        let shape = self.geometry.shape();
        if counts(response.and_msg_next_party()) != shape.and_msgs {
            return Err(WitnessError::AndMsgShape);
        }
        let well_formed = match response.input_share_2() {
            Some(x) => response.challenge().index() != 0 && counts(x) == shape.inputs,
            None => response.challenge().index() == 0,
        };
        if !well_formed {
            return Err(WitnessError::InputShareShape);
        }
        return Ok(());
    }

    /// Writes the witness of `response` into zeroed `z`, `a` and `b` words of one block.
    pub fn write_witness(
        &self,
        response: &Response<S, S>,
        z: &mut [u64],
        a: &mut [u64],
        b: &mut [u64],
    ) -> Result<(), WitnessError> {
        let g = &self.geometry;
        let shape = g.shape();
        let words = self.block_bits() / 64;
        assert!(z.len() == words && a.len() == words && b.len() == words);
        self.check_response(response)?;
        let challenge = response.challenge().index();
        let x_bits = match response.input_share_2() {
            Some(x) => crate::native::words_bits(x),
            None => vec![false; shape.input_bits()],
        };
        let m_bits = crate::native::words_bits(response.and_msg_next_party());
        let seeds = response.seeds();
        let set = |v: &mut [u64], c: u32, bit: bool| {
            let (w, s) = ((c >> 6) as usize, c & 63);
            v[w] = (v[w] & !(1u64 << s)) | ((bit as u64) << s);
        };
        let get = |v: &[u64], c: u32| (v[(c >> 6) as usize] >> (c & 63)) & 1 == 1;
        for step in &self.schedule {
            match *step {
                Step::Free(start, end) => {
                    for r in start as usize..end as usize {
                        let col = self.rows.cols[r];
                        let value = if col == CONST {
                            true
                        } else if col < h_col(3) {
                            col == h_col(challenge)
                        } else if col < g.x_col(0) {
                            let p = (col - g.seed_col(0, 0)) as usize;
                            bytes_bits(seeds[p / SEED_BITS].as_ref(), p % SEED_BITS)
                        } else if col < g.m_col(0) {
                            x_bits[(col - g.x_col(0)) as usize]
                        } else {
                            m_bits[(col - g.m_col(0)) as usize]
                        };
                        set(z, col, value);
                        set(a, col, value);
                        set(b, col, true);
                    }
                }
                Step::Rows(start, end) => {
                    for r in start as usize..end as usize {
                        let pa = self.row_a(r).iter().fold(false, |acc, &c| acc ^ get(z, c));
                        let pb = self.row_b(r).iter().fold(false, |acc, &c| acc ^ get(z, c));
                        let col = self.rows.cols[r];
                        set(a, col, pa);
                        set(b, col, pb);
                        set(z, col, pa & pb);
                    }
                }
                Step::Keccak(sub) => {
                    let base = (sub as usize) << SUB_LOG;
                    let local = base / 64..(base + SUB_BITS) / 64;
                    let s0 = base / 64 + keccak::STATE0_BASE / 64;
                    let initial: Lanes = core::array::from_fn(|l| z[s0 + l]);
                    keccak::write_witness(&initial, &mut z[local.clone()], &mut a[local.clone()], &mut b[local]);
                }
            }
        }
        return Ok(());
    }

    /// The lincheck's row-combination vector, folded over its `k_log − k_skip` sumcheck
    /// variables and evaluated from the block's structure rather than column by column.
    ///
    /// The dense route — [`LincheckCircuit::fold_alpha_batched`] followed by the verifier's
    /// sumcheck binding — computes
    /// `comb[c] = α·(Âᵀ·eq_row)[c] + (B̂ᵀ·eq_row)[c]` at all `2^k_log` columns and then folds it
    /// down to `2^k_skip` entries. Both halves are proportional to the block width. This returns
    /// the same `2^k_skip` entries without ever holding a vector over the columns, by splitting
    /// the block into its Keccak-f sub-blocks and its explicit rows:
    ///
    /// - every Keccak-f sub-block carries the same local matrix, so its fold is computed once and
    ///   re-weighted by `Σ_j eq_row_hi(j)·eq_col_hi(j)` over the sub-block indices, both `eq`
    ///   tables factorising across the sub-block boundary because it is aligned;
    /// - the explicit rows are paid one field multiplication per row and one per column slot each
    ///   row touches, their nonzeros costing only additions.
    ///
    /// `skip_weights` are the row weights on the skipped variables, `x_inner_rest` the row point
    /// and `r_inner_rest` the column point, both LSB-first as Flock orders them; `beta` is the
    /// constant-wire pin, which the dense route adds at the constant column before folding.
    pub fn comb_partial(
        &self,
        alpha: F128,
        beta: F128,
        skip_weights: &[F128],
        x_inner_rest: &[F128],
        r_inner_rest: &[F128],
    ) -> Vec<F128> {
        #[cfg(feature = "count")]
        let entry = flock_prover::field::gf2_128::op_count::snapshot().muls_excluding_inv();
        let mut out = self.comb_structured(alpha, beta, skip_weights, x_inner_rest, r_inner_rest);
        let explicit = self.comb_explicit(alpha, skip_weights, x_inner_rest, r_inner_rest);
        out.iter_mut().zip(explicit).for_each(|(o, e)| *o += e);
        #[cfg(feature = "count")]
        eprintln!(
            "[count] structured comb_partial: F128 muls {}",
            flock_prover::field::gf2_128::op_count::snapshot().muls_excluding_inv() - entry
        );
        return out;
    }

    /// The part of [`Self::comb_partial`] that the Keccak-f sub-blocks and the constant-wire pin
    /// contribute.
    pub fn comb_structured(
        &self,
        alpha: F128,
        beta: F128,
        skip_weights: &[F128],
        x_inner_rest: &[F128],
        r_inner_rest: &[F128],
    ) -> Vec<F128> {
        let n_skip = skip_weights.len();
        let k_skip = n_skip.trailing_zeros() as usize;
        assert!(n_skip == 1 << k_skip && k_skip <= 6 && k_skip < SUB_LOG);
        assert_eq!(x_inner_rest.len(), self.geometry.k_log() - k_skip);
        assert_eq!(r_inner_rest.len(), x_inner_rest.len());
        let mask = n_skip - 1;
        let lo = SUB_LOG - k_skip;
        let eq_row_lo = build_eq_table(&x_inner_rest[..lo]);
        let eq_row_hi = build_eq_table(&x_inner_rest[lo..]);
        let eq_col_hi = build_eq_table(&r_inner_rest[lo..]);
        let eq_col_lo = build_eq_table(&r_inner_rest[..lo]);
        let mut out = vec![F128::ZERO; n_skip];
        let eq_local: Vec<F128> = (0..SUB_BITS).map(|p| skip_weights[p & mask] * eq_row_lo[p >> k_skip]).collect();
        let mut local = flock_prover::alloc_zeroed_vec::<F128>(SUB_BITS);
        let konst_local = keccak::fold_shared(alpha, &eq_local, &mut local);
        let (first, subs) = (self.geometry.head_subs(), self.geometry.keccak_subs());
        let mut weight = F128::ZERO;
        let mut weight_konst = F128::ZERO;
        for j in first..first + subs {
            weight += eq_row_hi[j] * eq_col_hi[j];
            weight_konst += eq_row_hi[j];
        }
        for (s, o) in out.iter_mut().enumerate() {
            let mut acc = F128::ZERO;
            for (q, &e) in eq_col_lo.iter().enumerate() {
                acc += e * local[s + (q << k_skip)];
            }
            *o = weight * acc;
        }
        let eq_const = eq_col_lo[CONST as usize >> k_skip] * eq_col_hi[CONST as usize >> SUB_LOG];
        out[CONST as usize & mask] += (weight_konst * konst_local + beta) * eq_const;
        return out;
    }

    /// `Σ_s z[s]·comb_structured[s]`: the structured part of a matrix claim paired with the
    /// collapsed witness `z`, computed from the Keccak-f fold's rotation-invariant form and closed
    /// sums over the sub-block range.
    pub fn structured_value(
        &self,
        alpha: F128,
        beta: F128,
        skip: &[F128],
        z: &[F128],
        x_inner_rest: &[F128],
        r_inner_rest: &[F128],
    ) -> F128 {
        assert!(skip.len() == 64 && z.len() == 64, "the structured value assumes a 6-bit skip");
        let lo = SUB_LOG - 6;
        let row = build_eq_table(&x_inner_rest[..lo]);
        let col = build_eq_table(&r_inner_rest[..lo]);
        let (value, konst) = keccak::fold_shared_paired(alpha, skip, &row, z, &col);
        let (x_hi, r_hi) = (&x_inner_rest[lo..], &r_inner_rest[lo..]);
        let (first, subs) = (self.geometry.head_subs(), self.geometry.keccak_subs());
        let both: Vec<(F128, F128)> = x_hi
            .iter()
            .zip(r_hi)
            .map(|(&a, &b)| ((F128::ONE + a) * (F128::ONE + b), a * b))
            .collect();
        let rows: Vec<(F128, F128)> = x_hi.iter().map(|&a| (F128::ONE + a, a)).collect();
        let weight = product_range_sum(&both, first, first + subs);
        let weight_konst = product_range_sum(&rows, first, first + subs);
        let eq_const = col[0] * r_hi.iter().fold(F128::ONE, |acc, &b| acc * (F128::ONE + b));
        return weight * value + z[CONST as usize & 63] * eq_const * (weight_konst * konst + beta);
    }

    /// The part of [`Self::comb_partial`] that the explicit rows contribute.
    pub fn comb_explicit(&self, alpha: F128, skip_weights: &[F128], x_inner_rest: &[F128], r_inner_rest: &[F128]) -> Vec<F128> {
        let n_skip = skip_weights.len();
        let k_skip = n_skip.trailing_zeros() as usize;
        let mask = n_skip - 1;
        let eq_row_rest = build_eq_table(x_inner_rest);
        let eq_col_rest = build_eq_table(r_inner_rest);
        // The A and B sides are accumulated apart so that α multiplies once at the end rather
        // than once per row, and a row whose B side is the bare constant wire — every row but a
        // replay product — contributes its weight to one running scalar instead of a product.
        let rows = self.rows.cols.len();
        let (side_a, side_b) = (0..rows.div_ceil(EXPLICIT_CHUNK))
            .into_par_iter()
            .map(|c| {
                let (start, end) = (c * EXPLICIT_CHUNK, ((c + 1) * EXPLICIT_CHUNK).min(rows));
                let mut acc = (vec![F128::ZERO; n_skip], vec![F128::ZERO; n_skip]);
                let mut konst = F128::ZERO;
                let mut row = (vec![F128::ZERO; n_skip], vec![F128::ZERO; n_skip]);
                for r in start..end {
                    let col = self.rows.cols[r] as usize;
                    let e = skip_weights[col & mask] * eq_row_rest[col >> k_skip];
                    if e == F128::ZERO {
                        continue;
                    }
                    let (mut touched_a, mut touched_b) = (0u64, 0u64);
                    for &c in self.row_a(r) {
                        row.0[c as usize & mask] += eq_col_rest[c as usize >> k_skip];
                        touched_a |= 1 << (c as usize & mask);
                    }
                    if self.row_b(r) == [CONST] {
                        konst += e;
                    } else {
                        for &c in self.row_b(r) {
                            row.1[c as usize & mask] += eq_col_rest[c as usize >> k_skip];
                            touched_b |= 1 << (c as usize & mask);
                        }
                    }
                    while touched_a != 0 {
                        let s = touched_a.trailing_zeros() as usize;
                        touched_a &= touched_a - 1;
                        acc.0[s] += e * row.0[s];
                        row.0[s] = F128::ZERO;
                    }
                    while touched_b != 0 {
                        let s = touched_b.trailing_zeros() as usize;
                        touched_b &= touched_b - 1;
                        acc.1[s] += e * row.1[s];
                        row.1[s] = F128::ZERO;
                    }
                }
                acc.1[CONST as usize & mask] += konst * eq_col_rest[CONST as usize >> k_skip];
                acc
            })
            .reduce(
                || (vec![F128::ZERO; n_skip], vec![F128::ZERO; n_skip]),
                |mut x, y| {
                    x.0.iter_mut().zip(y.0).for_each(|(a, b)| *a += b);
                    x.1.iter_mut().zip(y.1).for_each(|(a, b)| *a += b);
                    x
                },
            );
        return side_a.into_iter().zip(side_b).map(|(a, b)| alpha * a + b).collect();
    }

    /// `Σ_{r,c} eq(row, r)·eq(col, c)·M[r, c]` for `M` the block's `A` (`a_side`) or `B` matrix,
    /// row `r` being the constraint that defines column `r`.
    pub fn bilinear_eq(&self, a_side: bool, row: &[F128], col: &[F128]) -> F128 {
        let skip = build_eq_table(&row[..6]);
        let col_lo = build_eq_table(&col[..6]);
        let pair = |alpha: F128| -> F128 {
            self.comb_partial(alpha, F128::ZERO, &skip, &row[6..], &col[6..])
                .iter()
                .zip(&col_lo)
                .fold(F128::ZERO, |acc, (&x, &e)| acc + x * e)
        };
        let b = pair(F128::ZERO);
        return if a_side { pair(F128::ONE) + b } else { b };
    }

    /// The block's `A` (`a_side`) or `B` matrix.
    pub fn matrix(&self, a_side: bool) -> BlockMatrix<'_> {
        return BlockMatrix { program: self, a_side };
    }

    /// The published words of a block's witness.
    pub fn io_words(&self, z: &[u64]) -> Vec<F128> {
        return self
            .geometry
            .io_word_cols()
            .into_iter()
            .map(|c| F128::new(z[2 * c], z[2 * c + 1]))
            .collect();
    }
}

/// `Σ_{a ≤ j < b} Π_i g_i(bit i of j)` for `g_i(0), g_i(1)` given as pairs, in time linear in the
/// number of bits.
pub fn product_range_sum(g: &[(F128, F128)], a: usize, b: usize) -> F128 {
    assert!(a <= b && b <= 1 << g.len());
    return prefix_product_sum(g, b) + prefix_product_sum(g, a);
}

/// `Σ_{j < n} Π_i g_i(bit i of j)`.
fn prefix_product_sum(g: &[(F128, F128)], n: usize) -> F128 {
    let k = g.len();
    if n == 1 << k {
        return g.iter().fold(F128::ONE, |acc, &(p, q)| acc * (p + q));
    }
    let mut full = vec![F128::ONE; k + 1];
    for i in 0..k {
        full[i + 1] = full[i] * (g[i].0 + g[i].1);
    }
    let mut acc = F128::ZERO;
    let mut high = F128::ONE;
    for i in (0..k).rev() {
        let bit = (n >> i) & 1;
        if bit == 1 {
            acc += high * g[i].0 * full[i];
            high *= g[i].1;
        } else {
            high *= g[i].0;
        }
    }
    return acc;
}

impl LincheckCircuit for Program {
    fn n_cols(&self) -> usize {
        return self.block_bits();
    }

    fn fold_alpha_batched(&self, alpha: F128, eq_inner: &[F128]) -> Vec<F128> {
        assert_eq!(eq_inner.len(), self.block_bits());
        #[cfg(feature = "count")]
        let entry = flock_prover::field::gf2_128::op_count::snapshot().muls_excluding_inv();
        let timing = std::env::var_os("POFSEED_TIMING").is_some();
        let t = std::time::Instant::now();
        let mut comb = flock_prover::alloc_zeroed_vec::<F128>(self.block_bits());
        for r in 0..self.rows.cols.len() {
            let e = eq_inner[self.rows.cols[r] as usize];
            if e == F128::ZERO {
                continue;
            }
            let ae = alpha * e;
            for &c in self.row_a(r) {
                comb[c as usize] += ae;
            }
            for &c in self.row_b(r) {
                comb[c as usize] += e;
            }
        }
        if timing {
            eprintln!("[pofseed] fold: explicit rows {:.2} s", t.elapsed().as_secs_f64());
        }
        let t = std::time::Instant::now();
        let first = self.geometry.head_subs() * SUB_BITS;
        let end = first + self.geometry.keccak_subs() * SUB_BITS;
        let konst: F128 = comb[first..end]
            .par_chunks_mut(SUB_BITS)
            .zip(eq_inner[first..end].par_chunks(SUB_BITS))
            .map(|(c, e)| keccak::fold_shared(alpha, e, c))
            .reduce(|| F128::ZERO, |x, y| x + y);
        comb[CONST as usize] += konst;
        if timing {
            eprintln!("[pofseed] fold: Keccak sub-blocks {:.2} s", t.elapsed().as_secs_f64());
        }
        #[cfg(feature = "count")]
        eprintln!(
            "[count] dense fold_alpha_batched: F128 muls {}",
            flock_prover::field::gf2_128::op_count::snapshot().muls_excluding_inv() - entry
        );
        return comb;
    }

    fn const_pin_col(&self) -> Option<usize> {
        return Some(CONST as usize);
    }
}

/// One side of a block's constraint matrices, row `r` being the constraint that defines column `r`.
pub struct BlockMatrix<'a> {
    program: &'a Program,
    a_side: bool,
}

impl FoldMatrix for BlockMatrix<'_> {
    fn row_marginal(&self, w: &[F128], n_rows: usize) -> Vec<F128> {
        let p = self.program;
        let n = p.block_bits();
        assert!(w.len() == n && n_rows == n);
        let mut out = flock_prover::alloc_zeroed_vec::<F128>(n);
        let rows = p.rows.cols.len();
        let explicit: Vec<(u32, F128)> = (0..rows)
            .into_par_iter()
            .map(|r| {
                let side = if self.a_side { p.row_a(r) } else { p.row_b(r) };
                (p.rows.cols[r], side.iter().fold(F128::ZERO, |acc, &c| acc + w[c as usize]))
            })
            .collect();
        for (col, v) in explicit {
            out[col as usize] = v;
        }
        let first = p.geometry.head_subs() * SUB_BITS;
        let end = first + p.geometry.keccak_subs() * SUB_BITS;
        let w_konst = w[CONST as usize];
        out[first..end].par_chunks_mut(SUB_BITS).zip(w[first..end].par_chunks(SUB_BITS)).for_each(|(o, local)| {
            for (dst, v) in o.iter_mut().zip(keccak::row_fold(self.a_side, local, w_konst)) {
                *dst += v;
            }
        });
        return out;
    }

    fn col_marginal(&self, w: &[F128], _n_cols: usize) -> Vec<F128> {
        let b = self.program.fold_alpha_batched(F128::ZERO, w);
        if !self.a_side {
            return b;
        }
        let ab = self.program.fold_alpha_batched(F128::ONE, w);
        return ab.into_par_iter().zip(b.into_par_iter()).map(|(x, y)| x + y).collect();
    }

    fn n_rows(&self) -> usize {
        return self.program.block_bits();
    }

    fn n_cols(&self) -> usize {
        return self.program.block_bits();
    }
}
