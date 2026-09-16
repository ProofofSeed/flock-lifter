// SPDX-License-Identifier: LGPL-3.0-or-later

//! Compilation of a ZKBoo circuit's two-party view replay into rows of the response block.
//!
//! The compiler is a ZKBoo [`Backend`]: running a circuit over it executes the replay of
//! `zkboo::verifier::replay::ViewReplayerBackend` symbolically, with every wire held as a linear
//! form per bit per opened slot. Linear gates act on the forms; every two-party AND product
//! becomes a committed column; the challenge enters through the one-hot bits `h₀, h₁, h₂`.

use crate::{
    form::{CONST, Form},
    layout::{Geometry, WIDTHS, h_col},
};
use zkboo::{
    backend::Backend,
    circuit::Circuit,
    word::{CompositeWord, Word, WordIdx},
};

/// Linear forms longer than this are materialised into a fresh column.
pub const MAX_FORM_LEN: usize = 32;

/// A row defining one column: `z[col] = A(z)·B(z)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    /// The column the row defines.
    pub col: u32,
    /// The A-side form.
    pub a: Form,
    /// The B-side form.
    pub b: Form,
}

/// The compiled replay of one circuit.
#[derive(Clone, Debug)]
pub struct Replay {
    /// Rows in evaluation order.
    pub rows: Vec<Row>,
    /// Bits absorbed into each slot's view commitment after its prefix, in order.
    pub streams: [Vec<Form>; 2],
    /// Bits of each slot's output share, widths 8, 32 and 64 in turn.
    pub outputs: [Vec<Form>; 2],
    /// First head column the replay left unused.
    pub end_col: u32,
    /// Committed two-party AND products.
    pub products: usize,
    /// Materialised linear forms.
    pub materialised: usize,
    /// The origin of every column from the replay base on: gate, column kind within the gate,
    /// and bit; `u32::MAX` marks a column no gate uses.
    pub origins: Vec<(u32, u8, u16)>,
}

fn width_index<W: Word>() -> usize {
    return WIDTHS
        .iter()
        .position(|&w| w == W::WIDTH)
        .unwrap_or_else(|| panic!("unsupported word width {}", W::WIDTH));
}

#[derive(Debug, Default)]
struct Pool {
    values: Vec<Option<[Vec<Form>; 2]>>,
    refcounts: Vec<usize>,
    free: Vec<usize>,
}

#[derive(Debug)]
struct Compiler<'g> {
    geometry: &'g Geometry,
    next_col: u32,
    rows: Vec<Row>,
    pools: [Pool; 3],
    streams: [Vec<Form>; 2],
    outputs: [[Vec<Form>; 2]; 3],
    input_tape_bits: usize,
    gate_tape_bits: usize,
    x_words: [usize; 3],
    m_words: [usize; 3],
    products: usize,
    materialised: usize,
    gate: u32,
    origin: (u8, u16),
    origins: Vec<(u32, u8, u16)>,
    regular: bool,
    base: u32,
    words: std::collections::HashMap<(u32, u8, u16), u32>,
}

impl<'g> Compiler<'g> {
    fn new(geometry: &'g Geometry) -> Self {
        return Self {
            geometry,
            next_col: geometry.replay_base(),
            rows: Vec::new(),
            pools: Default::default(),
            streams: Default::default(),
            outputs: Default::default(),
            input_tape_bits: 0,
            gate_tape_bits: 0,
            x_words: [0; 3],
            m_words: [0; 3],
            products: 0,
            materialised: 0,
            gate: 0,
            origin: (0, 0),
            origins: Vec::new(),
            regular: false,
            base: geometry.replay_base(),
            words: std::collections::HashMap::new(),
        };
    }

    fn fresh_col(&mut self) -> u32 {
        let (kind, bit) = self.origin;
        if self.regular {
            let key = (self.gate, kind, bit >> 6);
            let words = self.words.len() as u32;
            let word = *self.words.entry(key).or_insert(words);
            let col = self.base + (word << 6) + (bit & 63) as u32;
            let at = (col - self.base) as usize;
            if self.origins.len() <= at {
                self.origins.resize(at + 1, (u32::MAX, 0, 0));
            }
            assert_eq!(self.origins[at].0, u32::MAX, "a regular column is allocated twice");
            self.origins[at] = (self.gate, kind, bit);
            self.next_col = self.next_col.max(self.base + ((self.words.len() as u32) << 6));
            return col;
        }
        let col = self.next_col;
        self.next_col += 1;
        self.origins.push((self.gate, kind, bit));
        return col;
    }

    fn product(&mut self, l: &Form, r: &Form) -> Form {
        if self.regular {
            let col = self.fresh_col();
            self.rows.push(Row {
                col,
                a: l.clone(),
                b: r.clone(),
            });
            self.products += 1;
            return Form::col(col);
        }
        if l.is_zero() || r.is_zero() {
            return Form::zero();
        }
        if l.is_one() {
            return r.clone();
        }
        if r.is_one() {
            return l.clone();
        }
        let col = self.fresh_col();
        self.rows.push(Row {
            col,
            a: l.clone(),
            b: r.clone(),
        });
        self.products += 1;
        return Form::col(col);
    }

    fn cap(&mut self, f: Form) -> Form {
        if self.regular || f.len() <= MAX_FORM_LEN {
            return f;
        }
        return self.materialise(f);
    }

    /// Materialises `f` into a fresh column.
    fn materialise(&mut self, f: Form) -> Form {
        let col = self.fresh_col();
        self.rows.push(Row {
            col,
            a: f,
            b: Form::col(CONST),
        });
        self.materialised += 1;
        return Form::col(col);
    }

    /// Starts a gate that may allocate columns.
    fn begin(&mut self) {
        self.gate += 1;
    }

    /// Tags the columns allocated next with their kind within the gate and their bit.
    fn at(&mut self, kind: usize, bit: usize) {
        self.origin = (kind as u8, bit as u16);
    }

    fn read<W: Word, const N: usize>(&self, idx: WordIdx<W, N>) -> [Vec<Form>; 2] {
        let pool = &self.pools[width_index::<W>()];
        let mut out: [Vec<Form>; 2] = Default::default();
        for i in idx.into_array() {
            let value = pool.values[i].as_ref().expect("read of an unwritten word");
            for s in 0..2 {
                out[s].extend_from_slice(&value[s]);
            }
        }
        return out;
    }

    fn write<W: Word, const N: usize>(&mut self, idx: WordIdx<W, N>, value: [Vec<Form>; 2]) {
        let w = W::WIDTH;
        let pool = &mut self.pools[width_index::<W>()];
        for (limb, i) in idx.into_array().into_iter().enumerate() {
            pool.values[i] = Some([
                value[0][limb * w..(limb + 1) * w].to_vec(),
                value[1][limb * w..(limb + 1) * w].to_vec(),
            ]);
        }
    }

    fn map_bits<W: Word, const N: usize>(
        &mut self,
        in_: WordIdx<W, N>,
        out: WordIdx<W, N>,
        f: impl Fn(&[Form], usize) -> Form,
    ) {
        let v = self.read(in_);
        let res = v.map(|bits| (0..bits.len()).map(|b| f(&bits, b)).collect());
        self.write(out, res);
    }

    fn challenge_const<W: Word, const N: usize>(
        &mut self,
        in_: WordIdx<W, N>,
        mask: CompositeWord<W, N>,
        out: WordIdx<W, N>,
    ) {
        let v = self.read(in_);
        let mask = composite_bits(mask);
        let sel = [Form::col(h_col(0)), Form::col(h_col(2))];
        let mut res: [Vec<Form>; 2] = Default::default();
        self.begin();
        for s in 0..2 {
            let forms: Vec<Form> = v[s].iter().enumerate().map(|(b, f)| if mask[b] { f.xor(&sel[s]) } else { f.clone() }).collect();
            let all = forms.iter().any(|g| g.len() > MAX_FORM_LEN);
            for (b, g) in forms.into_iter().enumerate() {
                self.at(s, b);
                let g = if self.regular { if all { self.materialise(g) } else { g } } else { self.cap(g) };
                res[s].push(g);
            }
        }
        self.write(out, res);
    }

    fn gate_tape(&self, slot: usize, b: usize) -> Form {
        return Form::col(self.geometry.gate_tape_col(slot, self.gate_tape_bits + b));
    }

    fn m_offset<W: Word>(&self) -> usize {
        let t = width_index::<W>();
        let shape = self.geometry.shape();
        return (0..t).map(|u| shape.and_msgs[u] * WIDTHS[u]).sum::<usize>() + self.m_words[t] * W::WIDTH;
    }

    fn x_offset<W: Word>(&self) -> usize {
        let t = width_index::<W>();
        let shape = self.geometry.shape();
        return (0..t).map(|u| shape.inputs[u] * WIDTHS[u]).sum::<usize>() + self.x_words[t] * W::WIDTH;
    }
}

fn composite_bits<W: Word, const N: usize>(word: CompositeWord<W, N>) -> Vec<bool> {
    let mut bits = Vec::with_capacity(W::WIDTH * N);
    for limb in word.to_le_words() {
        let one: W = W::ONE;
        for b in 0..W::WIDTH {
            bits.push((limb >> b) & one == one);
        }
    }
    return bits;
}

impl<'g> Backend for Compiler<'g> {
    type FinalizeArg = ();
    type FinalizeResult = Replay;

    fn finalize(self, _arg: ()) -> Replay {
        let outputs = [0, 1].map(|s| {
            self.outputs
                .iter()
                .flat_map(|by_slot| by_slot[s].iter().cloned())
                .collect()
        });
        return Replay {
            rows: self.rows,
            streams: self.streams,
            outputs,
            end_col: self.next_col,
            products: self.products,
            materialised: self.materialised,
            origins: self.origins,
        };
    }

    fn input<W: Word, const N: usize>(&mut self, _word: CompositeWord<W, N>) -> WordIdx<W, N> {
        assert_eq!(
            self.gate_tape_bits, 0,
            "the block requires every input before the first AND gate"
        );
        let width = W::WIDTH * N;
        let x_base = self.x_offset::<W>();
        let mut res: [Vec<Form>; 2] = Default::default();
        let selectors = [
            Form::from_cols(vec![h_col(0), h_col(1)]),
            Form::from_cols(vec![h_col(0), h_col(2)]),
        ];
        self.begin();
        for b in 0..width {
            let x = Form::col(self.geometry.x_col(x_base + b));
            for s in 0..2 {
                self.at(s, b);
                let tape = Form::col(self.geometry.input_tape_col(s, self.input_tape_bits + b));
                let diff = tape.xor(&x);
                let p = self.product(&selectors[s], &diff);
                let v = x.xor(&p);
                self.streams[s].push(v.clone());
                res[s].push(v);
            }
        }
        self.input_tape_bits += width;
        self.x_words[width_index::<W>()] += N;
        let idx = self.alloc::<W, N>();
        self.write(idx, res);
        return idx;
    }

    fn alloc<W: Word, const N: usize>(&mut self) -> WordIdx<W, N> {
        let pool = &mut self.pools[width_index::<W>()];
        let idxs: [usize; N] = core::array::from_fn(|_| match pool.free.pop() {
            Some(i) => i,
            None => {
                pool.values.push(None);
                pool.refcounts.push(0);
                pool.values.len() - 1
            }
        });
        return WordIdx::new(idxs);
    }

    fn constant<W: Word, const N: usize>(&mut self, word: CompositeWord<W, N>, out: WordIdx<W, N>) {
        let bits: Vec<Form> = composite_bits(word).into_iter().map(Form::constant).collect();
        self.write(out, [bits.clone(), bits]);
    }

    fn from_le_words<W: Word, const N: usize>(&mut self, ins: [WordIdx<W, 1>; N], out: WordIdx<W, N>) {
        let mut res: [Vec<Form>; 2] = Default::default();
        for i in ins {
            let v = self.read(i);
            for s in 0..2 {
                res[s].extend_from_slice(&v[s]);
            }
        }
        self.write(out, res);
    }

    fn to_le_words<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, outs: [WordIdx<W, 1>; N]) {
        let v = self.read(in_);
        for (limb, o) in outs.into_iter().enumerate() {
            let w = W::WIDTH;
            self.write(o, [
                v[0][limb * w..(limb + 1) * w].to_vec(),
                v[1][limb * w..(limb + 1) * w].to_vec(),
            ]);
        }
    }

    fn output<W: Word, const N: usize>(&mut self, out: WordIdx<W, N>) {
        let v = self.read(out);
        let t = width_index::<W>();
        for s in 0..2 {
            self.outputs[t][s].extend_from_slice(&v[s]);
        }
    }

    fn increase_refcount<W: Word, const N: usize>(&mut self, idx: WordIdx<W, N>) {
        let pool = &mut self.pools[width_index::<W>()];
        for i in idx.into_array() {
            pool.refcounts[i] += 1;
        }
    }

    fn decrease_refcount<W: Word, const N: usize>(&mut self, idx: WordIdx<W, N>) {
        let pool = &mut self.pools[width_index::<W>()];
        for i in idx.into_array() {
            pool.refcounts[i] = pool.refcounts[i]
                .checked_sub(1)
                .expect("reference count underflow");
            if pool.refcounts[i] == 0 {
                pool.free.push(i);
            }
        }
    }

    fn not<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, out: WordIdx<W, N>) {
        self.challenge_const(in_, CompositeWord::<W, N>::MAX, out);
    }

    fn bitxor<W: Word, const N: usize>(&mut self, inl: WordIdx<W, N>, inr: WordIdx<W, N>, out: WordIdx<W, N>) {
        let l = self.read(inl);
        let r = self.read(inr);
        let mut res: [Vec<Form>; 2] = Default::default();
        self.begin();
        for s in 0..2 {
            let forms: Vec<Form> = (0..l[s].len()).map(|b| l[s][b].xor(&r[s][b])).collect();
            let all = forms.iter().any(|f| f.len() > MAX_FORM_LEN);
            for (b, f) in forms.into_iter().enumerate() {
                self.at(s, b);
                let f = if self.regular { if all { self.materialise(f) } else { f } } else { self.cap(f) };
                res[s].push(f);
            }
        }
        self.write(out, res);
    }

    fn bitand<W: Word, const N: usize>(&mut self, inl: WordIdx<W, N>, inr: WordIdx<W, N>, out: WordIdx<W, N>) {
        let l = self.read(inl);
        let r = self.read(inr);
        let width = W::WIDTH * N;
        let m_base = self.m_offset::<W>();
        let mut res: [Vec<Form>; 2] = Default::default();
        self.begin();
        for b in 0..width {
            self.at(0, b);
            let p00 = self.product(&l[0][b], &r[0][b]);
            self.at(1, b);
            let p01 = self.product(&l[0][b], &r[1][b]);
            self.at(2, b);
            let p10 = self.product(&l[1][b], &r[0][b]);
            self.at(3, b);
            let p11 = self.product(&l[1][b], &r[1][b]);
            let tapes = self.gate_tape(0, b).xor(&self.gate_tape(1, b));
            let o0 = p00.xor(&p01).xor(&p10).xor(&tapes);
            self.at(4, b);
            let o0 = if self.regular { self.materialise(o0) } else { self.cap(o0) };
            let m = Form::col(self.geometry.m_col(m_base + b));
            self.at(5, b);
            let o1 = p11.xor(&m);
            let o1 = if self.regular { self.materialise(o1) } else { self.cap(o1) };
            self.streams[0].push(o0.clone());
            self.streams[1].push(o1.clone());
            res[0].push(o0);
            res[1].push(o1);
        }
        self.gate_tape_bits += width;
        self.m_words[width_index::<W>()] += N;
        self.write(out, res);
    }

    fn bitxor_const<W: Word, const N: usize>(&mut self, inl: WordIdx<W, N>, inr: CompositeWord<W, N>, out: WordIdx<W, N>) {
        self.challenge_const(inl, inr, out);
    }

    fn bitand_const<W: Word, const N: usize>(&mut self, inl: WordIdx<W, N>, inr: CompositeWord<W, N>, out: WordIdx<W, N>) {
        let mask = composite_bits(inr);
        self.map_bits(inl, out, |bits, b| if mask[b] { bits[b].clone() } else { Form::zero() });
    }

    fn unbounded_shl<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, shift: usize, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| if b >= shift { bits[b - shift].clone() } else { Form::zero() });
    }

    fn unbounded_shr<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, shift: usize, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| {
            if b + shift < bits.len() { bits[b + shift].clone() } else { Form::zero() }
        });
    }

    fn rotate_left<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, shift: usize, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| {
            let w = bits.len();
            bits[(b + w - shift % w) % w].clone()
        });
    }

    fn rotate_right<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, shift: usize, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| bits[(b + shift) % bits.len()].clone());
    }

    fn reverse_bits<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| bits[bits.len() - 1 - b].clone());
    }

    fn swap_bytes<W: Word, const N: usize>(&mut self, in_: WordIdx<W, N>, out: WordIdx<W, N>) {
        self.map_bits(in_, out, |bits, b| {
            let bytes = bits.len() / 8;
            bits[8 * (bytes - 1 - b / 8) + b % 8].clone()
        });
    }

    fn cast<W: Word, T: Word>(&mut self, in_: WordIdx<W, 1>, out: WordIdx<T, 1>) {
        let v = self.read(in_);
        let res = v.map(|bits| {
            (0..T::WIDTH)
                .map(|b| if b < bits.len() { bits[b].clone() } else { Form::zero() })
                .collect()
        });
        self.write(out, res);
    }

    fn carry<W: Word, const N: usize>(&mut self, p: WordIdx<W, N>, g: WordIdx<W, N>, carry_in: bool, out: WordIdx<W, N>) {
        let ps = self.read(p);
        let gs = self.read(g);
        let width = W::WIDTH * N;
        let m_base = self.m_offset::<W>();
        let mut cs = [Form::constant(carry_in), Form::constant(carry_in)];
        let mut res: [Vec<Form>; 2] = Default::default();
        self.begin();
        for b in 0..width {
            res[0].push(cs[0].clone());
            res[1].push(cs[1].clone());
            if b + 1 == width {
                break;
            }
            self.at(0, b);
            let x01 = self.product(&cs[0], &ps[1][b]);
            self.at(1, b);
            let x10 = self.product(&cs[1], &ps[0][b]);
            self.at(2, b);
            let x00 = self.product(&cs[0], &ps[0][b]);
            self.at(3, b);
            let x11 = self.product(&cs[1], &ps[1][b]);
            let tapes = self.gate_tape(0, b).xor(&self.gate_tape(1, b));
            let n0 = x00.xor(&x01).xor(&x10).xor(&tapes).xor(&gs[0][b]);
            let m = Form::col(self.geometry.m_col(m_base + b));
            let n1 = x11.xor(&m).xor(&gs[1][b]);
            self.at(4, b);
            let c0 = if self.regular { self.materialise(n0) } else { self.cap(n0) };
            self.at(5, b);
            let c1 = if self.regular { self.materialise(n1) } else { self.cap(n1) };
            cs = [c0, c1];
        }
        self.streams[0].extend_from_slice(&res[0]);
        self.streams[1].extend_from_slice(&res[1]);
        self.gate_tape_bits += width;
        self.m_words[width_index::<W>()] += N;
        self.write(out, res);
    }
}

/// Compiles the replay of `circuit` with every gate laid out the same way at every bit: no
/// product is skipped for a constant operand, a gate's forms are materialised at all its bits or
/// at none, and every column kind of every gate limb has its own 64-bit word, bit `b` at column
/// `b` of the word. The result need not fit the geometry's head.
pub fn compile_regular<C: Circuit>(circuit: &C, geometry: &Geometry) -> Replay {
    let mut compiler = Compiler::new(geometry);
    compiler.regular = true;
    compiler.base = geometry.replay_base().next_multiple_of(64);
    compiler.next_col = compiler.base;
    let frontend = compiler.into_frontend();
    circuit.exec(&frontend);
    return frontend.finalize();
}

/// Compiles the uniform replay of `circuit` against `geometry`, or returns the head bits it needs
/// if the head is too small.
pub fn compile_regular_fitting<C: Circuit>(circuit: &C, geometry: &Geometry) -> Result<Replay, usize> {
    let replay = compile_regular(circuit, geometry);
    let shape = geometry.shape();
    assert_eq!(replay.streams[0].len(), shape.stream_bits(), "stream length disagrees with the shape");
    assert_eq!(replay.outputs[0].len(), shape.output_bits(), "output length disagrees with the shape");
    let needed = replay.end_col as usize;
    if needed > geometry.head_bits() {
        return Err(needed);
    }
    return Ok(replay);
}

/// Compiles the replay of `circuit` against `geometry`, or returns the head bits it needs if the
/// head is too small.
pub fn compile<C: Circuit>(circuit: &C, geometry: &Geometry) -> Result<Replay, usize> {
    let frontend = Compiler::new(geometry).into_frontend();
    circuit.exec(&frontend);
    let replay = frontend.finalize();
    let shape = geometry.shape();
    assert_eq!(replay.streams[0].len(), shape.stream_bits(), "stream length disagrees with the shape");
    assert_eq!(replay.outputs[0].len(), shape.output_bits(), "output length disagrees with the shape");
    let needed = replay.end_col as usize;
    if needed > geometry.head_bits() {
        return Err(needed);
    }
    return Ok(replay);
}
