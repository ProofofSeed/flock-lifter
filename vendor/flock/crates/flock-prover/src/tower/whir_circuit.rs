// Added to the vendored copy of Flock; see VENDORED.md at the vendored root.
//! The in-circuit verifier of a WHIR opening over GF(2^128) words with GF(2^256) challenges, as the
//! `flock-whir` crate proves it: driven by a recorded verification and the proof's openings.
//!
//! Every relation of the native verifier is arithmetised: the claims' γ-combination, every sumcheck
//! round over GF(2^256), each committed function's Merkle openings up to the root its cap hashes
//! to, the folding of every opened row by the round's challenges, the query coordinates derived
//! from the sampled position bits, the out-of-domain and shift constraints, the final polynomial
//! against the final openings, and the last claim against the final polynomial and the combined
//! weight. Grinding checks are the transcript's, emitted by the caller over the whole tape.

use std::any::Any;

use flock_core::{circuit::builder::SlotId, field::F256};
use flock_transcript::transcript_record::{
    RecordingChallenger, Stream, StreamWord, TranscriptOp as Op,
};

use crate::{
    r1cs_hashes::fs_chain::{FsChainTrace, IV},
    tower::{
        CHUNK_END, CHUNK_START, CollapsedSlots, F128, FsChallenger, PARENT, SLOT_WORDS,
        ShapeBuilder, Wire,
        child_walker::ChildSlots,
        cw, emit_fiat_shamir_chain, emit_recorded_pow_checks, flatten_ops,
        gates_spine::emit_mac256,
        hash_to_digest, pack_params, pack8, payload_words,
        rowmajor::{Consts, emit_eq_tensor256},
        squeeze_word_wire, walker_common,
    },
};

/// One committed function of a WHIR opening, as its verifier sees it.
pub struct WhirFunction {
    /// The sumcheck rounds that fold this function, and so the log of its row width.
    pub fold: usize,
    /// The log of its domain size.
    pub log_domain: usize,
    /// The queries into it.
    pub queries: usize,
    /// The variables of the function it is folded into, over which its queries' coordinates run.
    pub next_vars: usize,
    /// Its variables.
    pub vars: usize,
    /// Its out-of-domain samples.
    pub ood: usize,
    /// The normalised subspace table of its domain.
    pub table: Vec<Vec<F128>>,
    /// Whether its codeword is over GF(2^256).
    pub ext: bool,
    /// Its opened rows, as GF(2^128) words.
    pub rows: Vec<Vec<F128>>,
    /// Each opened row's Merkle path up to the cap.
    pub paths: Vec<Vec<[u8; 32]>>,
    /// Its cap.
    pub cap: Vec<[u8; 32]>,
}

/// A recorded WHIR verification and the proof data its circuit consumes.
pub struct WhirRecord {
    /// Every committed function, in round order.
    pub functions: Vec<WhirFunction>,
    /// The committed polynomial's variables.
    pub num_vars: usize,
    /// The final polynomial's variables.
    pub final_vars: usize,
    /// The evaluation claims opened.
    pub points: usize,
}

#[derive(Clone, Copy, Debug)]
struct Sq {
    fin: usize,
    ch: usize,
}

struct FnRec {
    cap_payload: usize,
    ood_points: Vec<Vec<Sq>>,
    ood_vals: Vec<usize>,
    /// The grinding-fused query squeeze into the previous function; absent for the first.
    queries: Option<Sq>,
    gamma: Option<Sq>,
    rounds: Vec<(usize, Sq)>,
}

/// A WHIR verification located on a recorded tape.
pub(super) struct WhirTape {
    config_payload: usize,
    fns: Vec<FnRec>,
    claim_points: Vec<Vec<usize>>,
    claim_vals: Vec<usize>,
    gamma0: Sq,
    final_poly_v: usize,
    final_queries: Sq,
    final_rounds: Vec<(usize, Sq)>,
}

fn vc_at(ops: &[Op], end: usize) -> (usize, usize) {
    let (mut v, mut c) = (0usize, 0usize);
    for op in &ops[..end] {
        match op {
            Op::SqueezeScalar => c += 1,
            Op::SqueezeSlice(n) => c += n,
            Op::ObserveScalar => v += 1,
            Op::ObserveSlice(n) => v += n,
            _ => {}
        }
    }
    (v, c)
}

fn fin_at(ops: &[Op], end: usize) -> usize {
    ops[..end].iter().filter(|o| o.finalizes()).count()
}

fn payload_at(ops: &[Op], end: usize) -> usize {
    ops[..end].iter().filter(|o| o.carries_payload()).count()
}

struct Cur<'a> {
    ops: &'a [Op],
    i: usize,
}

impl Cur<'_> {
    fn label(&mut self, l: &[u8]) {
        assert!(
            matches!(&self.ops[self.i], Op::Label(x) if x.as_slice() == l),
            "expected label {}, got {:?}",
            String::from_utf8_lossy(l),
            self.ops[self.i]
        );
        self.i += 1;
    }

    fn bytes(&mut self) -> usize {
        assert!(
            matches!(self.ops[self.i], Op::ObserveBytes(_)),
            "expected observed bytes, got {:?}",
            self.ops[self.i]
        );
        let p = payload_at(self.ops, self.i);
        self.i += 1;
        p
    }

    fn observe(&mut self, n: usize) -> usize {
        assert!(
            matches!(self.ops[self.i], Op::ObserveSlice(k) if k == n),
            "expected a {n}-slice observe, got {:?}",
            self.ops[self.i]
        );
        let v = vc_at(self.ops, self.i).0;
        self.i += 1;
        v
    }

    fn squeeze(&mut self, n: usize) -> Sq {
        while matches!(self.ops[self.i], Op::Pow { .. }) {
            self.i += 1;
        }
        assert!(
            matches!(self.ops[self.i], Op::SqueezeSlice(k) if k == n),
            "expected a {n}-slice squeeze, got {:?}",
            self.ops[self.i]
        );
        let sq = Sq {
            fin: fin_at(self.ops, self.i),
            ch: vc_at(self.ops, self.i).1,
        };
        self.i += 1;
        sq
    }

    fn rounds(&mut self, n: usize) -> Vec<(usize, Sq)> {
        (0..n)
            .map(|_| {
                let g = self.observe(2);
                assert_eq!(
                    self.observe(2),
                    g + 2,
                    "a round's two messages are adjacent"
                );
                (g, self.squeeze(2))
            })
            .collect()
    }
}

impl WhirTape {
    /// The byte-payload ordinals of every committed function's cap, in round order.
    pub(super) fn cap_payloads(&self) -> Vec<usize> {
        self.fns.iter().map(|f| f.cap_payload).collect()
    }

    /// The byte-payload ordinal of the configuration.
    pub(super) fn config_payload(&self) -> usize {
        self.config_payload
    }

    /// Locates the WHIR verification that starts at op `start` of a flattened tape.
    pub(super) fn parse(ops: &[Op], start: usize, rec: &WhirRecord) -> (WhirTape, usize) {
        let mut cur = Cur { ops, i: start };
        cur.label(b"flock-whir-v1");
        let config_payload = cur.bytes();
        let mut fns = Vec::with_capacity(rec.functions.len());
        let m = rec.num_vars;
        let f0 = &rec.functions[0];
        let cap_payload = cur.bytes();
        let ood_points: Vec<Vec<Sq>> = (0..f0.ood)
            .map(|_| (0..m).map(|_| cur.squeeze(2)).collect())
            .collect();
        let ood_vals: Vec<usize> = (0..f0.ood).map(|_| cur.observe(2)).collect();
        cur.label(b"flock-whir-open");
        cur.bytes();
        let mut claim_points = Vec::with_capacity(rec.points);
        let mut claim_vals = Vec::with_capacity(rec.points);
        for _ in 0..rec.points {
            claim_points.push((0..m).map(|_| cur.observe(2)).collect());
            claim_vals.push(cur.observe(2));
        }
        let gamma0 = cur.squeeze(2);
        let rounds = cur.rounds(f0.fold);
        fns.push(FnRec {
            cap_payload,
            ood_points,
            ood_vals,
            queries: None,
            gamma: None,
            rounds,
        });
        for f in &rec.functions[1..] {
            let cap_payload = cur.bytes();
            let ood_points: Vec<Vec<Sq>> = (0..f.ood)
                .map(|_| (0..f.vars).map(|_| cur.squeeze(2)).collect())
                .collect();
            let ood_vals: Vec<usize> = (0..f.ood).map(|_| cur.observe(2)).collect();
            let prev_q = rec.functions[fns.len() - 1].queries;
            let queries = Some(cur.squeeze(prev_q));
            let gamma = Some(cur.squeeze(2));
            let rounds = cur.rounds(f.fold);
            fns.push(FnRec {
                cap_payload,
                ood_points,
                ood_vals,
                queries,
                gamma,
                rounds,
            });
        }
        let final_poly_v = cur.observe(2);
        for _ in 1..1usize << rec.final_vars {
            cur.observe(2);
        }
        let final_queries = cur.squeeze(rec.functions.last().unwrap().queries);
        let final_rounds = cur.rounds(rec.final_vars);
        (
            WhirTape {
                config_payload,
                fns,
                claim_points,
                claim_vals,
                gamma0,
                final_poly_v,
                final_queries,
                final_rounds,
            },
            cur.i,
        )
    }
}

/// The wires a WHIR circuit reads from its enclosing transcript's emission.
pub(super) struct WhirWires<'a> {
    pub(super) outs: &'a [Vec<Wire>],
    pub(super) trace: &'a FsChainTrace,
    pub(super) stream: &'a Stream,
    pub(super) ww: &'a [Option<Wire>],
    pub(super) vmap: &'a [Option<usize>],
    pub(super) chals: &'a [F128],
    pub(super) vals_rec: &'a [F128],
}

impl WhirWires<'_> {
    fn wv(&self, vi: usize) -> Wire {
        self.ww[self.vmap[vi].expect("stream word")].expect("wired")
    }
    fn wv2(&self, vi: usize) -> [Wire; 2] {
        [self.wv(vi), self.wv(vi + 1)]
    }
    fn sq2(&self, s: Sq) -> [Wire; 2] {
        [
            squeeze_word_wire(self.outs, self.trace, s.fin, 0),
            squeeze_word_wire(self.outs, self.trace, s.fin, 1),
        ]
    }
    fn sq_word(&self, s: Sq, j: usize) -> Wire {
        squeeze_word_wire(self.outs, self.trace, s.fin, j)
    }
    fn n2(&self, s: Sq) -> F256 {
        F256::new(self.chals[s.ch], self.chals[s.ch + 1])
    }
    fn v2(&self, vi: usize) -> F256 {
        F256::new(self.vals_rec[vi], self.vals_rec[vi + 1])
    }
    fn payload(&self, p: usize) -> Vec<Wire> {
        payload_words(self.stream)[p]
            .iter()
            .map(|&wi| self.ww[wi].expect("payload word wired"))
            .collect()
    }
}

/// A term of the running weight: its coefficient wires and native value, and its kind.
enum Term {
    Eq([Wire; 2], F256, Vec<([Wire; 2], F256)>),
    Shift([Wire; 2], F256, Vec<(Wire, F128)>),
}

/// The Merkle root of a cap: `2^c` node pairs hashed pairwise up to one.
fn emit_cap_root(
    sb: &mut ShapeBuilder,
    b3: SlotId,
    iv: [Wire; 2],
    cap: &[[Wire; 2]],
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> [Wire; 2] {
    let mut layer = cap.to_vec();
    while layer.len() > 1 {
        let params = cw(sb, vals, consts, pack_params(0, 64, PARENT));
        layer = layer
            .chunks(2)
            .map(|p| {
                let out = sb.gate(
                    b3,
                    &[iv[0], iv[1], p[0][0], p[0][1], p[1][0], p[1][1], params],
                );
                [out[0], out[1]]
            })
            .collect();
    }
    layer[0]
}

/// A leaf hashed as one BLAKE3 chunk and climbed through `depth` levels to the root, the
/// siblings as swap hints; returns the root and the position's bits.
#[allow(clippy::too_many_arguments)]
fn emit_full_opening(
    sb: &mut ShapeBuilder,
    s: CollapsedSlots,
    iv: [Wire; 2],
    leaf_w: &[Wire],
    index_w: Wire,
    depth: usize,
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> ([Wire; 2], Vec<Wire>) {
    let blocks = leaf_w.len().div_ceil(4);
    assert!(blocks <= 16, "a leaf is one BLAKE3 chunk (<= 1024 bytes)");
    let zero_w = cw(sb, vals, consts, F128::ZERO);
    let mask: u128 = (1u128 << depth) - 1;
    let mask_w = cw(
        sb,
        vals,
        consts,
        F128::new(mask as u64, (mask >> 64) as u64),
    );
    let spread = sb.gate(s.spread, &[index_w, zero_w, zero_w, mask_w, zero_w]);
    let bits: Vec<Wire> = spread[..depth].to_vec();
    let mut cv = iv;
    for i in 0..blocks {
        let mut flags = 0u32;
        if i == 0 {
            flags |= CHUNK_START;
        }
        if i + 1 == blocks {
            flags |= CHUNK_END;
        }
        let words = (leaf_w.len() - 4 * i).min(4);
        let params = cw(sb, vals, consts, pack_params(0, 16 * words as u32, flags));
        let mw = |j: usize| if j < words { leaf_w[4 * i + j] } else { zero_w };
        let out = sb.gate(s.b3, &[cv[0], cv[1], mw(0), mw(1), mw(2), mw(3), params]);
        cv = [out[0], out[1]];
    }
    for &bit in bits.iter().take(depth) {
        let sw = sb.gate_hinted(s.swap, &[bit, cv[0], cv[1]]);
        let params = cw(sb, vals, consts, pack_params(0, 64, PARENT));
        let out = sb.gate(s.b3, &[iv[0], iv[1], sw[0], sw[1], sw[2], sw[3], params]);
        cv = [out[0], out[1]];
    }
    (cv, bits)
}

/// The full leaf-to-root sibling path of leaf `pos`: the proof's path to the cap, then the cap
/// tree's own siblings.
fn full_path(path: &[[u8; 32]], cap: &[[u8; 32]], pos: usize, depth: usize) -> Vec<[u8; 32]> {
    use flock_merkle::{Blake3MerkleHash, MerkleHash};
    let c = cap.len().trailing_zeros() as usize;
    assert_eq!(path.len(), depth - c, "the proof's path stops at the cap");
    let mut out = path.to_vec();
    let mut layer = cap.to_vec();
    let mut idx = pos >> (depth - c);
    while layer.len() > 1 {
        out.push(layer[idx ^ 1]);
        layer = layer
            .chunks(2)
            .map(|p| Blake3MerkleHash::hash_pair(&p[0], &p[1]))
            .collect();
        idx >>= 1;
    }
    out
}

/// Emits the verifier of the WHIR opening located by `tape`, whose claim points and values are the
/// stream words the tape observed; returns the claim wires `(points, values)` for the caller to
/// bind.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_whir_verifier(
    sb: &mut ShapeBuilder,
    cs: &ChildSlots,
    iv: [Wire; 2],
    tape: &WhirTape,
    rec: &WhirRecord,
    w: &WhirWires<'_>,
    k: Consts,
    vals: &mut Vec<F128>,
    hints: &mut Vec<[u32; SLOT_WORDS]>,
    consts: &mut Vec<(F128, Wire)>,
) -> (Vec<Vec<[Wire; 2]>>, Vec<[Wire; 2]>) {
    let mac256 = cs
        .resid
        .iter()
        .find(|&&(key, _)| key == 701)
        .expect("the F256 MAC slot")
        .1;
    let macs = cs.macs;
    let (zw, ow, zassert) = (k.zw, k.ow, k.zassert);
    let z2 = [zw, zw];
    let one2 = [ow, zw];
    let mul = |sb: &mut ShapeBuilder, x: [Wire; 2], y: [Wire; 2]| emit_mac256(sb, mac256, z2, x, y);
    let add =
        |sb: &mut ShapeBuilder, x: [Wire; 2], y: [Wire; 2]| emit_mac256(sb, mac256, x, y, one2);
    let assert_zero = |sb: &mut ShapeBuilder, x: [Wire; 2]| {
        sb.connect(x[0], zassert);
        sb.connect(x[1], zassert);
    };
    let _ = tape.config_payload;
    // ---- the claims' combination ----
    let f0 = &tape.fns[0];
    let mut value_vs: Vec<usize> = f0.ood_vals.clone();
    value_vs.extend(&tape.claim_vals);
    let g0_w = w.sq2(tape.gamma0);
    let g0_n = w.n2(tape.gamma0);
    let mut pw_w = g0_w;
    let mut pw_n = g0_n;
    let mut claim_w = z2;
    let mut claim_n = F256::ZERO;
    let mut terms: Vec<Term> = Vec::new();
    let mut eq_points: Vec<Vec<([Wire; 2], F256)>> = f0
        .ood_points
        .iter()
        .map(|p| p.iter().map(|&s| (w.sq2(s), w.n2(s))).collect())
        .collect();
    eq_points.extend(
        tape.claim_points
            .iter()
            .map(|p| p.iter().map(|&v| (w.wv2(v), w.v2(v))).collect::<Vec<_>>()),
    );
    for (j, &vi) in value_vs.iter().enumerate() {
        claim_w = emit_mac256(sb, mac256, claim_w, pw_w, w.wv2(vi));
        claim_n += pw_n * w.v2(vi);
        terms.push(Term::Eq(pw_w, pw_n, eq_points[j].clone()));
        if j + 1 < value_vs.len() {
            pw_w = mul(sb, pw_w, g0_w);
            pw_n *= g0_n;
        }
    }
    // ---- a sumcheck round: claim' = a + (b + e∞·r)·r ----
    let round = |sb: &mut ShapeBuilder, claim_w: [Wire; 2], claim_n: F256, g: usize, s: Sq| {
        let (e1, einf) = (w.wv2(g), w.wv2(g + 2));
        let (e1n, einfn) = (w.v2(g), w.v2(g + 2));
        let r = w.sq2(s);
        let rn = w.n2(s);
        let a = add(sb, claim_w, e1);
        let b = add(sb, claim_w, einf);
        let t = emit_mac256(sb, mac256, b, einf, r);
        let out = emit_mac256(sb, mac256, a, t, r);
        let (an, bn) = (claim_n + e1n, claim_n + einfn);
        (out, an + (bn + einfn * rn) * rn, (r, rn))
    };
    let mut challenges: Vec<([Wire; 2], F256)> = Vec::with_capacity(rec.num_vars);
    let mut alpha: Vec<([Wire; 2], F256)> = Vec::new();
    for &(g, s) in &f0.rounds {
        let (cw2, cn, r) = round(sb, claim_w, claim_n, g, s);
        (claim_w, claim_n) = (cw2, cn);
        alpha.push(r);
        challenges.push(r);
    }
    // ---- per committed function: its cap root, its queries' openings, folds and coordinates ----
    let open_queries = |sb: &mut ShapeBuilder,
                        vals: &mut Vec<F128>,
                        hints: &mut Vec<[u32; SLOT_WORDS]>,
                        consts: &mut Vec<(F128, Wire)>,
                        fi: usize,
                        qsq: Sq,
                        alpha: &[([Wire; 2], F256)]|
     -> Vec<([Wire; 2], F256, Vec<(Wire, F128)>)> {
        let f = &rec.functions[fi];
        let fr = &tape.fns[fi];
        let cap_words = w.payload(fr.cap_payload);
        let cap_pairs: Vec<[Wire; 2]> = cap_words.chunks(2).map(|c| [c[0], c[1]]).collect();
        let root = emit_cap_root(sb, cs.q.b3, iv, &cap_pairs, vals, consts);
        let eq_w = emit_eq_tensor256(
            sb,
            mac256,
            &alpha.iter().map(|&(x, _)| x).collect::<Vec<_>>(),
            k,
        );
        let eq_n = {
            let mut t = vec![F256::ONE];
            for &(_, r) in alpha {
                let old = t;
                t = old
                    .iter()
                    .map(|&x| x * (F256::ONE + r))
                    .chain(old.iter().map(|&x| x * r))
                    .collect();
            }
            t
        };
        let lanes = 1usize << f.fold;
        (0..f.queries)
            .map(|q| {
                let word_n = w.chals[qsq.ch + q];
                let pos = (word_n.lo as usize) & ((1usize << f.log_domain) - 1);
                vals.extend_from_slice(&f.rows[q]);
                let leaf_w: Vec<Wire> = (0..f.rows[q].len()).map(|_| sb.input()).collect();
                let (r, bits) = emit_full_opening(
                    sb,
                    cs.q,
                    iv,
                    &leaf_w,
                    w.sq_word(qsq, q),
                    f.log_domain,
                    vals,
                    consts,
                );
                sb.connect(r[0], root[0]);
                sb.connect(r[1], root[1]);
                hints.extend(
                    full_path(&f.paths[q], &f.cap, pos, f.log_domain)
                        .iter()
                        .map(hash_to_digest),
                );
                let mut val_w = z2;
                let mut val_n = F256::ZERO;
                for l in 0..lanes {
                    let (e, en) = if f.ext {
                        (
                            [leaf_w[2 * l], leaf_w[2 * l + 1]],
                            F256::new(f.rows[q][2 * l], f.rows[q][2 * l + 1]),
                        )
                    } else {
                        ([leaf_w[l], zw], F256::new(f.rows[q][l], F128::ZERO))
                    };
                    val_w = emit_mac256(sb, mac256, val_w, eq_w[l], e);
                    val_n += eq_n[l] * en;
                }
                let coords: Vec<(Wire, F128)> = (0..f.next_vars)
                    .map(|i| {
                        let mut acc = bits[i];
                        let mut acc_n = if (pos >> i) & 1 == 1 {
                            F128::ONE
                        } else {
                            F128::ZERO
                        };
                        for j in i + 1..f.log_domain {
                            let c = f.table[i][j - i];
                            let c_w = cw(sb, vals, consts, c);
                            acc = sb.gate(macs, &[acc, bits[j], c_w])[0];
                            if (pos >> j) & 1 == 1 {
                                acc_n += c;
                            }
                        }
                        (acc, acc_n)
                    })
                    .collect();
                (val_w, val_n, coords)
            })
            .collect()
    };
    for fi in 1..rec.functions.len() {
        let f = &rec.functions[fi];
        let fr = &tape.fns[fi];
        let folded = open_queries(sb, vals, hints, consts, fi - 1, fr.queries.unwrap(), &alpha);
        let gs = fr.gamma.unwrap();
        let (g_w, g_n) = (w.sq2(gs), w.n2(gs));
        let (mut pw_w, mut pw_n) = (g_w, g_n);
        let n_terms = f.ood + folded.len();
        let mut j = 0;
        let mut step = |sb: &mut ShapeBuilder, pw_w: &mut [Wire; 2], pw_n: &mut F256| {
            j += 1;
            if j < n_terms {
                *pw_w = mul(sb, *pw_w, g_w);
                *pw_n *= g_n;
            }
        };
        for (z, &vi) in fr.ood_points.iter().zip(&fr.ood_vals) {
            claim_w = emit_mac256(sb, mac256, claim_w, pw_w, w.wv2(vi));
            claim_n += pw_n * w.v2(vi);
            terms.push(Term::Eq(
                pw_w,
                pw_n,
                z.iter().map(|&s| (w.sq2(s), w.n2(s))).collect(),
            ));
            step(sb, &mut pw_w, &mut pw_n);
        }
        for (val_w, val_n, coords) in folded {
            claim_w = emit_mac256(sb, mac256, claim_w, pw_w, val_w);
            claim_n += pw_n * val_n;
            terms.push(Term::Shift(pw_w, pw_n, coords));
            step(sb, &mut pw_w, &mut pw_n);
        }
        alpha.clear();
        for &(g, s) in &fr.rounds {
            let (cw2, cn, r) = round(sb, claim_w, claim_n, g, s);
            (claim_w, claim_n) = (cw2, cn);
            alpha.push(r);
            challenges.push(r);
        }
    }
    // ---- the final polynomial against the final openings ----
    let n_final = 1usize << rec.final_vars;
    let final_w: Vec<[Wire; 2]> = (0..n_final)
        .map(|i| w.wv2(tape.final_poly_v + 2 * i))
        .collect();
    let final_n: Vec<F256> = (0..n_final)
        .map(|i| w.v2(tape.final_poly_v + 2 * i))
        .collect();
    let last = rec.functions.len() - 1;
    let folded = open_queries(sb, vals, hints, consts, last, tape.final_queries, &alpha);
    for (val_w, val_n, coords) in folded {
        let mut f_w = final_w.clone();
        let mut f_n = final_n.clone();
        for &(c_w, c_n) in &coords {
            f_w = f_w
                .chunks(2)
                .map(|p| emit_mac256(sb, mac256, p[0], [c_w, zw], p[1]))
                .collect();
            f_n = f_n
                .chunks(2)
                .map(|p| p[0] + p[1] * F256::new(c_n, F128::ZERO))
                .collect();
        }
        assert_eq!(
            f_n[0], val_n,
            "the final polynomial meets a final opening natively"
        );
        let d = add(sb, f_w[0], val_w);
        assert_zero(sb, d);
    }
    for &(g, s) in &tape.final_rounds {
        let (cw2, cn, r) = round(sb, claim_w, claim_n, g, s);
        (claim_w, claim_n) = (cw2, cn);
        challenges.push(r);
    }
    assert_eq!(challenges.len(), rec.num_vars, "one challenge per variable");
    // ---- the last claim: claim = f̂(r_final) · Σ terms ----
    let r_final = &challenges[challenges.len() - rec.final_vars..];
    let mut m_w = final_w;
    let mut m_n = final_n;
    for &(r, rn) in r_final {
        m_w = m_w
            .chunks(2)
            .map(|p| {
                let d = add(sb, p[0], p[1]);
                emit_mac256(sb, mac256, p[0], r, d)
            })
            .collect();
        m_n = m_n.chunks(2).map(|p| p[0] + rn * (p[0] + p[1])).collect();
    }
    let mut weight_w = z2;
    let mut weight_n = F256::ZERO;
    for t in &terms {
        match t {
            Term::Eq(c, cn, z) => {
                let suffix = &challenges[challenges.len() - z.len()..];
                let mut p_w = *c;
                let mut p_n = *cn;
                for (&(zw2, zn), &(rw, rn)) in z.iter().zip(suffix) {
                    let s = add(sb, zw2, rw);
                    let f = add(sb, s, one2);
                    p_w = mul(sb, p_w, f);
                    p_n *= F256::ONE + zn + rn;
                }
                weight_w = add(sb, weight_w, p_w);
                weight_n += p_n;
            }
            Term::Shift(c, cn, coords) => {
                let suffix = &challenges[challenges.len() - coords.len()..];
                let mut p_w = *c;
                let mut p_n = *cn;
                for (&(c_w, c_n), &(yw, yn)) in coords.iter().zip(suffix) {
                    let oc = sb.gate(macs, &[c_w, ow, ow])[0];
                    let f = emit_mac256(sb, mac256, one2, yw, [oc, zw]);
                    p_w = mul(sb, p_w, f);
                    p_n *= F256::ONE + yn * (F128::ONE + c_n);
                }
                weight_w = add(sb, weight_w, p_w);
                weight_n += p_n;
            }
        }
    }
    assert_eq!(
        claim_n,
        m_n[0] * weight_n,
        "the WHIR opening closes natively"
    );
    let d = emit_mac256(sb, mac256, claim_w, m_w[0], weight_w);
    assert_zero(sb, d);
    let points = tape
        .claim_points
        .iter()
        .map(|p| p.iter().map(|&v| w.wv2(v)).collect())
        .collect();
    let values = tape.claim_vals.iter().map(|&v| w.wv2(v)).collect();
    (points, values)
}

/// A standalone circuit verifying one recorded WHIR opening, built and run; returns the circuit's
/// BLAKE3 rows and every slot's largest row count.
pub fn build_whir_circuit(
    rec_ch: &RecordingChallenger<FsChallenger>,
    domain: &[u8],
    rec: &WhirRecord,
) -> (usize, usize) {
    let t_shape = rec_ch.shape();
    let ops: Vec<Op> = flatten_ops(t_shape.ops()).to_vec();
    let chals = rec_ch.challenges().to_vec();
    let vals_rec = rec_ch.values().to_vec();
    let mc = walker_common::merge_and_replay_chain(
        &t_shape,
        domain,
        rec_ch.values(),
        rec_ch.payloads(),
        &ops,
        &chals,
    );
    let start = ops
        .iter()
        .position(|o| matches!(o, Op::Label(l) if l.as_slice() == b"flock-whir-v1"))
        .expect("a WHIR verification on the tape");
    let (tape, end) = WhirTape::parse(&ops, start, rec);
    assert_eq!(end, ops.len(), "the WHIR verification ends the tape");
    let pub_payloads = vec![false; payload_at(&ops, ops.len())];
    let mut nu = 24usize;
    let mut measured = false;
    loop {
        let mut sb = ShapeBuilder::new(nu);
        let spread_w = rec.functions.iter().map(|f| f.log_domain).max().unwrap();
        let cs = ChildSlots::new(&mut sb, nu, spread_w);
        let mut vals: Vec<F128> = Vec::new();
        let mut hints: Vec<[u32; SLOT_WORDS]> = Vec::new();
        let mut consts: Vec<(F128, Wire)> = Vec::new();
        let k = Consts::new(&mut sb, &mut vals);
        let iv_w = pack8(&IV);
        let iv2 = [
            cw(&mut sb, &mut vals, &mut consts, iv_w[0]),
            cw(&mut sb, &mut vals, &mut consts, iv_w[1]),
        ];
        let (outs, ww) = emit_fiat_shamir_chain(
            &mut sb,
            cs.q.b3,
            iv2,
            &mc.trace,
            &mc.stream,
            &mc.bytes,
            &mut vals,
            &mut consts,
            &pub_payloads,
            &mc.cross,
        );
        emit_recorded_pow_checks(
            &mut sb,
            cs.q.b3,
            cs.q.pow,
            iv2,
            &ops,
            &mc.trace,
            &mc.stream,
            &outs,
            &ww,
            &mut vals,
            &mut consts,
        );
        let mut vmap: Vec<Option<usize>> = Vec::new();
        for (wi, word) in mc.stream.words.iter().enumerate() {
            if let StreamWord::Value(vi) = *word {
                if vmap.len() <= vi {
                    vmap.resize(vi + 1, None);
                }
                vmap[vi] = Some(wi);
            }
        }
        let wires = WhirWires {
            outs: &outs,
            trace: &mc.trace,
            stream: &mc.stream,
            ww: &ww,
            vmap: &vmap,
            chals: &chals,
            vals_rec: &vals_rec,
        };
        let _ = emit_whir_verifier(
            &mut sb,
            &cs,
            iv2,
            &tape,
            rec,
            &wires,
            k,
            &mut vals,
            &mut hints,
            &mut consts,
        );
        let mut need = [cs.q.b3, cs.q.swap, cs.q.spread, cs.q.pow, cs.macs]
            .iter()
            .map(|&s| sb.rows_in_slot(s))
            .max()
            .unwrap();
        for &(_, s) in cs.resid.iter() {
            need = need.max(sb.rows_in_slot(s));
        }
        if !measured {
            nu = (need.next_power_of_two().trailing_zeros() as usize).max(7);
            measured = true;
            continue;
        }
        let b3_rows = sb.rows_in_slot(cs.q.b3);
        let shape = sb.finish().expect("the WHIR circuit builds");
        let hint_refs: Vec<&(dyn Any + Sync)> =
            hints.iter().map(|h| h as &(dyn Any + Sync)).collect();
        let _ = shape.run(&vals, &hint_refs);
        return (b3_rows, need);
    }
}
