// SPDX-License-Identifier: LGPL-3.0-or-later

//! The response block as a program: its explicit rows, the order in which rows and Keccak-f
//! sub-blocks are evaluated, the witness of one response, and the structured lincheck fold.

use crate::{
    form::{CONST, Form},
    keccak::{self, Lanes, SUB_BITS, SUB_LOG},
    layout::{DIGEST_BITS, Geometry, RATE_BYTES, SEED_BITS, StatementShape, SubKind, VIEW_PREFIX_BYTES, h_col},
    replay::{self, Replay},
};
use flock_prover::{field::F128, lincheck::LincheckCircuit};
use pofseed_flock_lift_statement::S;
use rayon::prelude::*;
use zkboo::{
    circuit::Circuit,
    crypto::{TAG_PRG, TAG_VIEW_COMMITMENT},
    prover::proof::Response,
    word::{Word, Words},
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

fn words_bits(words: &Words) -> Vec<bool> {
    let mut bits = Vec::new();
    push_word_bits::<u8>(words, &mut bits);
    push_word_bits::<u32>(words, &mut bits);
    push_word_bits::<u64>(words, &mut bits);
    return bits;
}

fn push_word_bits<W: Word>(words: &Words, bits: &mut Vec<bool>) {
    for &w in words.as_vec::<W>() {
        let one: W = W::ONE;
        for b in 0..W::WIDTH {
            bits.push((w >> b) & one == one);
        }
    }
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
    /// Builds the block of `circuit`.
    pub fn new<C: Circuit>(circuit: &C) -> Self {
        let shape = StatementShape::of(circuit);
        let mut k_log = SUB_LOG + 1;
        let mut head_bits = 0;
        let (geometry, replay) = loop {
            let Some(geometry) = Geometry::new(shape.clone(), k_log, head_bits) else {
                k_log += 1;
                continue;
            };
            match replay::compile(circuit, &geometry) {
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

    fn row_a(&self, r: usize) -> &[u32] {
        return &self.rows.a_idx[self.rows.a_ptr[r] as usize..self.rows.a_ptr[r + 1] as usize];
    }

    fn row_b(&self, r: usize) -> &[u32] {
        return &self.rows.b_idx[self.rows.b_ptr[r] as usize..self.rows.b_ptr[r + 1] as usize];
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
        let msgs = response.and_msg_next_party();
        if counts(msgs) != shape.and_msgs {
            return Err(WitnessError::AndMsgShape);
        }
        let challenge = response.challenge().index();
        let x_bits = match response.input_share_2() {
            Some(x) if challenge != 0 && counts(x) == shape.inputs => words_bits(x),
            None if challenge == 0 => vec![false; shape.input_bits()],
            _ => return Err(WitnessError::InputShareShape),
        };
        let m_bits = words_bits(msgs);
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

impl LincheckCircuit for Program {
    fn n_cols(&self) -> usize {
        return self.block_bits();
    }

    fn fold_alpha_batched(&self, alpha: F128, eq_inner: &[F128]) -> Vec<F128> {
        assert_eq!(eq_inner.len(), self.block_bits());
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
        let first = self.geometry.head_subs() * SUB_BITS;
        let end = first + self.geometry.keccak_subs() * SUB_BITS;
        let konst: F128 = comb[first..end]
            .par_chunks_mut(SUB_BITS)
            .zip(eq_inner[first..end].par_chunks(SUB_BITS))
            .map(|(c, e)| keccak::fold_shared(alpha, e, c))
            .reduce(|| F128::ZERO, |x, y| x + y);
        comb[CONST as usize] += konst;
        return comb;
    }

    fn const_pin_col(&self) -> Option<usize> {
        return Some(CONST as usize);
    }
}
