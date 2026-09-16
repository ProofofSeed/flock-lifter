// SPDX-License-Identifier: LGPL-3.0-or-later

//! The machine's committed states and the witnesses of its steps, mirroring `OneStep.sol`: the
//! same hashes, the same calldata commitments, and the memory and calldata proofs in the order
//! the contract consumes them.

use std::sync::Arc;

use revm::primitives::{B256, U256, keccak256};

use crate::merkle::{levels, range_proof, words_of, zeros};

/// Depth of the memory tree.
pub const MEM_DEPTH: usize = 22;
/// Depth of a call's calldata prefix tree.
pub const PREFIX_DEPTH: usize = 10;
/// Depth of a call's calldata body tree.
pub const BODY_DEPTH: usize = 24;
/// What `GAS` pushes.
pub const GAS_CONSTANT: u64 = 1 << 32;
/// A running state.
pub const RUNNING: u64 = 0;
/// The accepting terminal state.
pub const ACCEPTED: u64 = 1;
/// The rejecting terminal state.
pub const REJECTED: u64 = 2;

fn w(v: U256) -> [u8; 32] {
    return v.to_be_bytes();
}

fn hash_words(words: &[[u8; 32]]) -> B256 {
    return keccak256(words.concat());
}

/// The hash of a terminal state.
pub fn terminal(kind: u64) -> B256 {
    let mut words = [[0u8; 32]; 8];
    words[0] = w(U256::from(kind));
    return hash_words(&words);
}

/// Opcodes the machine implements.
pub fn supported(op: u8) -> bool {
    return matches!(op, 0x00..=0x0b | 0x10..=0x1e | 0x20 | 0x30 | 0x32..=0x3a | 0x3d | 0x3e | 0x46 | 0x50..=0x53 | 0x56..=0x5b | 0x5e..=0xa4 | 0xf3 | 0xfa | 0xfd | 0xfe);
}

/// A call's calldata, committed as a prefix tree and a body tree over its argument words.
#[derive(Clone)]
pub struct CallData {
    /// The calldata.
    pub bytes: Vec<u8>,
    /// Argument words in the prefix tree.
    pub prefix_words: usize,
    prefix: Vec<Vec<B256>>,
    body: Arc<Vec<Vec<B256>>>,
    words: Vec<B256>,
}

impl CallData {
    /// Commits `bytes`, with the first `prefix_words` argument words in the prefix tree and the
    /// rest in the body tree, whose levels may be given if already built.
    pub fn new(bytes: Vec<u8>, prefix_words: usize, body: Option<Arc<Vec<Vec<B256>>>>) -> Self {
        assert!(bytes.len() >= 4 && (bytes.len() - 4) % 32 == 0, "calldata is a selector and whole words");
        let words = words_of(&bytes[4..]);
        let prefix = levels(&words[..prefix_words], PREFIX_DEPTH);
        let body = body.unwrap_or_else(|| Arc::new(levels(&words[prefix_words..], BODY_DEPTH)));
        return Self {
            bytes,
            prefix_words,
            prefix,
            body,
            words,
        };
    }

    /// The body tree's levels.
    pub fn body_levels(&self) -> Arc<Vec<Vec<B256>>> {
        return self.body.clone();
    }

    fn root(levels: &[Vec<B256>], depth: usize) -> B256 {
        return levels[depth].first().copied().unwrap_or(zeros(depth)[depth]);
    }

    /// The first five words of the call's context: length, selector, prefix root, prefix words,
    /// body root.
    pub fn commit(&self) -> [[u8; 32]; 5] {
        return [
            w(U256::from(self.bytes.len())),
            w(U256::from(u32::from_be_bytes(self.bytes[..4].try_into().expect("selector")))),
            Self::root(&self.prefix, PREFIX_DEPTH).0,
            w(U256::from(self.prefix_words)),
            Self::root(&self.body, BODY_DEPTH).0,
        ];
    }

    fn arg_words(&self) -> usize {
        return (self.bytes.len() - 4) / 32;
    }
}

/// A call's context: its calldata and the outputs of the calls before it.
#[derive(Clone)]
pub struct Ctx {
    /// Which call.
    pub call: usize,
    /// Its calldata.
    pub calldata: CallData,
    /// Earlier outputs.
    pub outputs: Vec<Vec<u8>>,
}

impl Ctx {
    /// The context preimage.
    pub fn words(&self) -> [[u8; 32]; 8] {
        let mut out = [[0u8; 32]; 8];
        out[..5].copy_from_slice(&self.calldata.commit());
        for (i, o) in self.outputs.iter().enumerate() {
            out[5 + i] = keccak256(o).0;
        }
        return out;
    }

    /// The context hash.
    pub fn hash(&self) -> B256 {
        return hash_words(&self.words());
    }
}

/// A running state as observed: program counter, stack (bottom first), memory and return data.
#[derive(Clone, Debug, Default)]
pub struct Snap {
    /// Program counter.
    pub pc: usize,
    /// Stack, bottom first.
    pub stack: Vec<U256>,
    /// Memory.
    pub memory: Vec<u8>,
    /// Return data.
    pub ret: Vec<u8>,
}

/// A state with its memory tree built.
pub struct Committed<'a> {
    /// The observed state.
    pub snap: &'a Snap,
    /// The memory tree's levels.
    pub mem: Vec<Vec<B256>>,
}

impl<'a> Committed<'a> {
    /// Builds the memory tree of `snap`.
    pub fn new(snap: &'a Snap) -> Self {
        return Self {
            snap,
            mem: levels(&words_of(&snap.memory), MEM_DEPTH),
        };
    }

    /// The memory root.
    pub fn mem_root(&self) -> B256 {
        return self.mem[MEM_DEPTH].first().copied().unwrap_or(zeros(MEM_DEPTH)[MEM_DEPTH]);
    }

    /// The stack hash.
    pub fn stack_hash(&self) -> B256 {
        let words: Vec<[u8; 32]> = self.snap.stack.iter().map(|v| w(*v)).collect();
        return hash_words(&words);
    }

    /// The state hash within `ctx`.
    pub fn hash(&self, ctx: &Ctx) -> B256 {
        return hash_words(&[
            w(U256::from(RUNNING)),
            w(U256::from(ctx.call)),
            w(U256::from(self.snap.pc)),
            w(U256::from(self.snap.memory.len())),
            self.mem_root().0,
            ctx.hash().0,
            keccak256(&self.snap.ret).0,
            self.stack_hash().0,
        ]);
    }

    /// The `pre` argument of the contract's step.
    pub fn pre(&self, ctx: &Ctx) -> [U256; 5] {
        return [
            U256::from(RUNNING),
            U256::from(ctx.call),
            U256::from(self.snap.pc),
            U256::from(self.snap.memory.len()),
            U256::from_be_bytes(self.mem_root().0),
        ];
    }
}

/// The hash of the state a call starts in.
pub fn start_hash(ctx: &Ctx) -> B256 {
    return Committed::new(&Snap::default()).hash(ctx);
}

/// A step's witness, section by section.
#[derive(Default, Debug)]
pub struct Witness {
    /// Memory proofs.
    pub mem: Vec<u8>,
    /// Calldata proofs.
    pub cd: Vec<u8>,
    /// Earlier outputs.
    pub outs: Vec<u8>,
    /// Words proved in all.
    pub words: usize,
}

impl Witness {
    /// The witness as the contract takes it.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for s in [&self.mem, &self.cd, &self.outs] {
            out.extend_from_slice(&w(U256::from(s.len())));
            out.extend_from_slice(s);
        }
        return out;
    }
}

fn push_entry(out: &mut Vec<u8>, lo: usize, values: &[B256], proof: &[B256]) {
    out.extend_from_slice(&w(U256::from(lo)));
    out.extend_from_slice(&w(U256::from(values.len())));
    for v in values {
        out.extend_from_slice(v.as_slice());
    }
    out.extend_from_slice(&w(U256::from(proof.len())));
    for p in proof {
        out.extend_from_slice(p.as_slice());
    }
}

fn level_word(levels: &[Vec<B256>], i: usize) -> B256 {
    return levels[0].get(i).copied().unwrap_or(B256::ZERO);
}

/// Builds the witness of one step.
pub struct StepWitness<'a> {
    state: &'a Committed<'a>,
    ctx: &'a Ctx,
    code: &'a [u8],
    /// The witness so far.
    pub witness: Witness,
}

impl<'a> StepWitness<'a> {
    /// A builder for the step from `state` in `ctx` running `code`.
    pub fn new(state: &'a Committed<'a>, ctx: &'a Ctx, code: &'a [u8]) -> Self {
        return Self {
            state,
            ctx,
            code,
            witness: Witness::default(),
        };
    }

    fn msize(&self) -> usize {
        return self.state.snap.memory.len();
    }

    fn mem_entry(&mut self, lo: usize, hi: usize) {
        let proof = range_proof(&self.state.mem, MEM_DEPTH, lo, hi);
        let values: Vec<B256> = (lo..hi).map(|i| level_word(&self.state.mem, i)).collect();
        push_entry(&mut self.witness.mem, lo, &values, &proof);
        self.witness.words += hi - lo;
    }

    /// Memory `[o, o + len)` read.
    pub fn read(&mut self, o: usize, len: usize) -> Vec<u8> {
        let mut data = vec![0u8; len];
        if len == 0 {
            return data;
        }
        let (lo, hi, top) = (o / 32, (o + len).div_ceil(32), self.msize() / 32);
        if lo >= top {
            return data;
        }
        let end = hi.min(top);
        self.mem_entry(lo, end);
        let mem = &self.state.snap.memory;
        let n = len.min(end * 32 - o);
        data[..n].copy_from_slice(&mem[o..o + n]);
        return data;
    }

    /// Memory `[o, o + len)` written with `data` then zeros.
    pub fn write(&mut self, o: usize, data: &[u8], len: usize) {
        if len == 0 {
            return;
        }
        let (lo, top) = (o / 32, self.msize() / 32);
        let mut end = (o + len).div_ceil(32);
        let from = if top * 32 > o { top * 32 - o } else { 0 };
        let nonzero = data.iter().skip(from).any(|&b| b != 0);
        if end > top && !nonzero {
            end = top;
        }
        if end <= lo {
            return;
        }
        self.mem_entry(lo, end);
    }

    fn cd_entry(&mut self, lo: usize, hi: usize, prefix: bool) {
        let cd = &self.ctx.calldata;
        let (levels, depth, base) = if prefix {
            (&cd.prefix, PREFIX_DEPTH, 0)
        } else {
            (&*cd.body, BODY_DEPTH, cd.prefix_words)
        };
        let proof = range_proof(levels, depth, lo - base, hi - base);
        let values: Vec<B256> = (lo..hi).map(|i| cd.words[i]).collect();
        push_entry(&mut self.witness.cd, lo, &values, &proof);
        self.witness.words += hi - lo;
    }

    /// Calldata `[o, o + n)`, which must lie within the calldata.
    pub fn calldata(&mut self, o: usize, n: usize) -> Vec<u8> {
        let cd = self.ctx.calldata.bytes.clone();
        if n == 0 {
            return Vec::new();
        }
        let at = 4usize.saturating_sub(o).min(n);
        if at < n {
            let first = o + at - 4;
            let (lo, hi) = (first / 32, (o + n - 4).div_ceil(32));
            let end = hi.min(self.ctx.calldata.arg_words());
            let p = self.ctx.calldata.prefix_words;
            if lo < end && lo < p {
                self.cd_entry(lo, end.min(p), true);
            }
            let b = lo.max(p);
            if b < end {
                self.cd_entry(b, end, false);
            }
        }
        return cd[o..o + n].to_vec();
    }

    /// The outputs `outs` of earlier calls, as the boundary step takes them.
    pub fn outputs(&mut self, outs: &[&[u8]]) {
        for o in outs {
            self.witness.outs.extend_from_slice(&w(U256::from(o.len())));
            let mut padded = o.to_vec();
            padded.resize(o.len().div_ceil(32) * 32, 0);
            self.witness.outs.extend_from_slice(&padded);
        }
    }

    /// Builds the witness of the step at the state's program counter. Returns the output if the
    /// step ends the call.
    pub fn build(mut self) -> (Witness, Option<Vec<u8>>) {
        let snap = self.state.snap;
        let op = self.code.get(snap.pc).copied().unwrap_or(0);
        let s = &snap.stack;
        let arg = |i: usize| -> U256 { s[s.len() - 1 - i] };
        let lim = U256::from(32u64 << MEM_DEPTH);
        let ok = |o: U256, len: U256| len.is_zero() || (o <= lim && len <= lim && o + len <= lim);
        let us = |v: U256| -> usize { if v > lim { 0 } else { v.to::<usize>() } };
        let cd_len = self.ctx.calldata.bytes.len();
        let mut output = None;
        if !supported(op) || s.len() < arity(op) {
            return (self.witness, None);
        }
        match op {
            0x00 => output = Some(Vec::new()),
            0x20 | 0xf3 | 0x51 => {
                let len = if op == 0x51 { U256::from(32) } else { arg(1) };
                if ok(arg(0), len) {
                    let data = if len.is_zero() { Vec::new() } else { self.read(us(arg(0)), us(len)) };
                    if op == 0xf3 {
                        output = Some(data);
                    }
                }
            }
            0x35 => {
                if arg(0) < U256::from(cd_len) {
                    let o = arg(0).to::<usize>();
                    self.calldata(o, (cd_len - o).min(32));
                }
            }
            0x37 | 0x39 | 0x3e => {
                let (dst, src, len) = (arg(0), arg(1), arg(2));
                let bad_ret = op == 0x3e && src.checked_add(len).is_none_or(|e| e > U256::from(snap.ret.len()));
                if !bad_ret && ok(dst, len) && !len.is_zero() {
                    let (dst, len) = (us(dst), us(len));
                    let data = match op {
                        0x37 if src < U256::from(cd_len) => {
                            let src = src.to::<usize>();
                            self.calldata(src, (cd_len - src).min(len))
                        }
                        0x39 if src < U256::from(self.code.len()) => {
                            let src = src.to::<usize>();
                            self.code[src..src + (self.code.len() - src).min(len)].to_vec()
                        }
                        0x3e => {
                            let src = src.to::<usize>();
                            snap.ret[src..src + len].to_vec()
                        }
                        _ => Vec::new(),
                    };
                    self.write(dst, &data, len);
                }
            }
            0x52 | 0x53 => {
                let len = if op == 0x52 { 32 } else { 1 };
                if ok(arg(0), U256::from(len)) {
                    let v = w(arg(1));
                    let data = if op == 0x52 { v.to_vec() } else { vec![v[31]] };
                    self.write(us(arg(0)), &data, len);
                }
            }
            0x5e => {
                let (dst, src, len) = (arg(0), arg(1), arg(2));
                if ok(src, len) && ok(dst, len) && !len.is_zero() {
                    let data = self.read(us(src), us(len));
                    self.write(us(dst), &data, us(len));
                }
            }
            0xfa => {
                let (g, to, ao, al, ro, rl) = (arg(0), arg(1), arg(2), arg(3), arg(4), arg(5));
                if ok(ao, al) && ok(ro, rl) && to == U256::from(2) {
                    let args = if al.is_zero() { Vec::new() } else { self.read(us(ao), us(al)) };
                    let cost = 60 + 12 * (us(al).div_ceil(32) as u64);
                    if g >= U256::from(cost) && !rl.is_zero() {
                        let out = sha2_digest::sha256(&args);
                        let n = us(rl).min(32);
                        self.write(us(ro), &out[..n], n);
                    }
                }
            }
            _ => {}
        }
        if output.is_some() {
            let outs: Vec<Vec<u8>> = match self.ctx.call {
                1 => vec![self.ctx.outputs[0].clone()],
                2 => vec![self.ctx.outputs[0].clone(), self.ctx.outputs[1].clone()],
                _ => Vec::new(),
            };
            let refs: Vec<&[u8]> = outs.iter().map(|o| o.as_slice()).collect();
            self.outputs(&refs);
        }
        return (self.witness, output);
    }
}

/// Stack items opcode `op` needs.
pub fn arity(op: u8) -> usize {
    return match op {
        0x01..=0x07 | 0x0a | 0x0b | 0x10..=0x14 | 0x16..=0x18 | 0x1a..=0x1d | 0x20 => 2,
        0x08 | 0x09 => 3,
        0x15 | 0x19 | 0x1e | 0x35 | 0x50 | 0x51 | 0x56 => 1,
        0x37 | 0x39 | 0x3e | 0x5e => 3,
        0x52 | 0x53 | 0x57 | 0xf3 | 0xfd => 2,
        0x80..=0x8f => (op - 0x7f) as usize,
        0x90..=0x9f => (op - 0x8e) as usize,
        0xa0..=0xa4 => (op - 0x9e) as usize,
        0xfa => 6,
        _ => 0,
    };
}

mod sha2_digest {
    /// SHA-256.
    pub fn sha256(data: &[u8]) -> [u8; 32] {
        use sha2::Digest;
        return sha2::Sha256::digest(data).into();
    }
}
