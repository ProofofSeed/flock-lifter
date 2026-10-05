// Added to the vendored copy of Flock; see VENDORED.md at the vendored root.
//! The recursive head: a lift, one union-circuit proof that a block's wrap verifies, published in
//! head form; and a head, one union-circuit proof that a lift or head and a new block's wrap verify.
//! Both fold their children's deferred claims and the previous accumulators into the accumulators
//! they publish.

use std::time::Instant;

use flock_core::{
    aggregate::{Accumulator, ElementMatrices},
    challenger::Challenger,
    circuit::SigmaAssertion,
    matrix_fold::{
        FoldGrinding, FoldMatrix, FoldProof, JaggedClaim, JaggedRowWeight, JaggedTable,
        MatrixClaim, Weight, col_marginal, prove_fold_jagged_with_grinding,
        prove_fold_with_grinding,
    },
    pcs::{LOG_PACKING, OuterPcs, jagged::JaggedParams},
    verifier::FlockVerifyError,
    zerocheck::{K_SKIP, multilinear::subspace_denominator_pair},
};
use flock_field::phi8::PHI_8_TABLE;
use flock_transcript::transcript_record::RecordingChallenger;

use crate::tower::{
    F128, FsChallenger, LeafOuter, MacGate, ShapeBuilder, UnionInstance, Wire, ZskipTapeRec,
    ZskipWires, cw, emit_lagrange_lows,
    head_env::{
        ENV_DOMAIN, EnvBuild, EnvCensus, EnvKey, EnvProof, HeadEnv, emit_assert_eq, prove_env,
        slot_list,
    },
    head_walker::{HeadRegion, HeadTape, emit_head_region},
    node::digest_f128,
    payload_words,
    rowmajor::{Consts, FoldEmit, FoldTape, emit_folds, emit_parent},
    whir_circuit::WhirRecord,
};

const HEAD_FOLD_DOMAIN: &[u8] = b"flock-head-fold-v0";

/// One proof a lift or head verifies: its key, the proof, its WHIR opening's record, where its
/// head block starts in its public segment, that block's layout (none for a wrap, whose block is
/// its digest and lincheck accumulators), and the commitment scheme it is opened through.
pub struct HeadChild<'a> {
    /// The circuit's key.
    pub key: &'a EnvKey,
    /// The proof.
    pub proof: &'a EnvProof,
    /// The WHIR opening's record.
    pub whir: &'a WhirRecord,
    /// Where the head block starts in the proof's public segment.
    pub block: usize,
    /// The head block's layout, for a lift or head.
    pub layout: Option<&'a HeadLayout>,
    /// The commitment scheme the proof is opened through.
    pub outer: &'a dyn OuterPcs,
}

/// One accumulator entry of a head block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Entry {
    /// A table group of the wrap circuit's registry.
    Wrap(usize),
    /// A table group of the heads' registry.
    Head(usize),
    /// The wiring slot of the wrap circuit.
    SigmaWrap,
    /// The wiring slot of the lift circuit.
    SigmaLift,
    /// The wiring slot of the previous lift or head.
    SigmaHead,
    /// The jagged slot of the wrap circuit's layout.
    JaggedWrap,
    /// The jagged slot of the heads' layout.
    JaggedHead,
}

/// The head block's layout, relative to its start: the chain value, the two lincheck
/// accumulators, the three wiring keys, then one `[live | ρ_col | ρ_row | value]` entry per
/// [`Entry`], in [`HeadLayout::entries`] order.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct HeadLayout {
    /// Column and row variables of the lincheck accumulators on `A` and `B`.
    pub lc: [(usize, usize); 2],
    /// Boolean table types of the wrap registry.
    pub n_wrap_bool: usize,
    /// Column and row variables per wrap-registry group: Boolean `A`/`B` per type, then element.
    pub wrap: Vec<(usize, usize)>,
    /// Boolean table types of the heads' registry.
    pub n_head_bool: usize,
    /// Column and row variables per head-registry group.
    pub head: Vec<(usize, usize)>,
    /// Column and row variables of the wrap circuit's wiring slot.
    pub sigma_wrap: (usize, usize),
    /// Column and row variables of the heads' wiring slots.
    pub sigma_head: (usize, usize),
    /// Column and row variables of the wrap layout's jagged slot.
    pub jagged_wrap: (usize, usize),
    /// Column and row variables of the heads' jagged slot.
    pub jagged_head: (usize, usize),
}

impl HeadLayout {
    /// Where lincheck accumulator `i` starts: `[ρ_col | ρ_row | value]`.
    pub fn lc_at(&self, i: usize) -> usize {
        2 + self.lc[..i].iter().map(|&(c, r)| c + r + 1).sum::<usize>()
    }

    /// Where the three wiring keys start: wrap, lift, previous head.
    pub fn keys_at(&self) -> usize {
        self.lc_at(2)
    }

    /// Every entry with its column and row variables, in block order.
    pub fn entries(&self) -> Vec<(Entry, (usize, usize))> {
        let mut v: Vec<(Entry, (usize, usize))> = Vec::new();
        v.extend(
            self.wrap
                .iter()
                .enumerate()
                .map(|(i, &w)| (Entry::Wrap(i), w)),
        );
        v.extend(
            self.head
                .iter()
                .enumerate()
                .map(|(i, &w)| (Entry::Head(i), w)),
        );
        v.push((Entry::SigmaWrap, self.sigma_wrap));
        v.push((Entry::SigmaLift, self.sigma_head));
        v.push((Entry::SigmaHead, self.sigma_head));
        v.push((Entry::JaggedWrap, self.jagged_wrap));
        v.push((Entry::JaggedHead, self.jagged_head));
        v
    }

    /// Where entry `e` starts and its column and row variables, if the layout has it.
    pub fn find(&self, e: Entry) -> Option<(usize, (usize, usize))> {
        let mut at = self.keys_at() + 6;
        for (x, (c, r)) in self.entries() {
            if x == e {
                return Some((at, (c, r)));
            }
            at += c + r + 2;
        }
        None
    }

    /// Where entry `e` starts and its column and row variables.
    pub fn locate(&self, e: Entry) -> (usize, (usize, usize)) {
        self.find(e)
            .unwrap_or_else(|| panic!("no entry {e:?} in the layout"))
    }

    /// The block's length.
    pub fn len(&self) -> usize {
        self.keys_at()
            + 6
            + self
                .entries()
                .iter()
                .map(|(_, (c, r))| c + r + 2)
                .sum::<usize>()
    }

    /// Whether the block is empty.
    pub fn is_empty(&self) -> bool {
        false
    }
}

/// What a lift's or head's verifier holds: the circuit's key, the head block's layout and start,
/// and what the circuit used of its envelope.
pub struct HeadKey {
    /// The circuit's key.
    pub key: EnvKey,
    /// The head block's layout.
    pub layout: HeadLayout,
    /// Where the head block starts in the public segment.
    pub block: usize,
    /// What the circuit used of its envelope.
    pub census: EnvCensus,
}

/// A lift or head proof.
pub type HeadProof = EnvProof;

/// Phase timings of a lift or head, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct HeadTimings {
    /// Verifying the children natively and parsing their transcripts.
    pub tapes: f64,
    /// Proving the fold natively.
    pub fold: f64,
    /// Building the circuit shape.
    pub build: f64,
    /// Running the witness.
    pub witness: f64,
    /// Proving the circuit.
    pub prove: f64,
}

/// A claim read from a public segment, `[live | ρ_col | ρ_row | value]`, zero past its end.
fn read_entry(public: &[F128], at: usize, kc: usize, kr: usize) -> MatrixClaim {
    let get = |i: usize| public.get(i).copied().unwrap_or(F128::ZERO);
    let live = get(at);
    MatrixClaim {
        row: Weight::low_eq(vec![live], (0..kr).map(|j| get(at + 1 + kc + j)).collect()),
        col: Weight::low_eq(vec![live], (0..kc).map(|j| get(at + 1 + j)).collect()),
        value: get(at + 1 + kc + kr),
    }
}

/// A lincheck accumulator read from a public segment, `[ρ_col | ρ_row | value]`.
fn read_lc(public: &[F128], at: usize, kc: usize, kr: usize) -> MatrixClaim {
    MatrixClaim {
        row: Weight::eq(public[at + kc..at + kc + kr].to_vec()),
        col: Weight::eq(public[at..at + kc].to_vec()),
        value: public[at + kc + kr],
    }
}

/// The zero claim with the given variables.
fn dead(kc: usize, kr: usize) -> MatrixClaim {
    MatrixClaim {
        row: Weight::low_eq(vec![F128::ZERO], vec![F128::ZERO; kr]),
        col: Weight::low_eq(vec![F128::ZERO], vec![F128::ZERO; kc]),
        value: F128::ZERO,
    }
}

fn payload_values(t: &HeadTape<'_>, p: usize) -> Vec<F128> {
    payload_words(&t.stream)[p]
        .iter()
        .map(|&wi| {
            let b = &t.bytes[wi * 16..wi * 16 + 16];
            F128::new(
                u64::from_le_bytes(b[..8].try_into().unwrap()),
                u64::from_le_bytes(b[8..].try_into().unwrap()),
            )
        })
        .collect()
}

/// Which child a claim comes from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kid {
    A,
    B,
}

/// The routing gate a previous entry's low is scaled by.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Low {
    /// The entry's own live word.
    Live,
    /// `live · [key = A's circuit]`: the previous head slot staying put.
    Stay,
    /// `live · [key ≠ A's circuit]`: the previous head slot moving to the lift slot.
    Move,
}

/// Where one folded claim comes from, which the circuit ties its surface to.
#[derive(Clone, Copy, Debug)]
enum Tie {
    /// A previous accumulator entry in `A`'s public segment.
    Entry { at: usize, low: Low },
    /// The zero claim.
    Dead,
    /// A lincheck accumulator `[ρ_col | ρ_row | value]` in a child's public segment.
    Lc { kid: Kid, at: usize },
    /// A child's Boolean table claim.
    Bool { kid: Kid, t: usize, side: usize },
    /// A child's element table claim.
    El { kid: Kid, t: usize, side: usize },
    /// A child's circuit-structure claim.
    Sigma { kid: Kid, j: usize },
}

/// Where one jagged group's claims come from.
#[derive(Clone, Copy, Debug)]
enum JTie {
    /// A previous jagged entry in `A`'s public segment.
    Entry { at: usize },
    /// The zero claim.
    Dead,
    /// Every jagged claim of a child.
    Fresh { kid: Kid },
}

/// What a published entry is.
#[derive(Clone, Copy, Debug)]
enum Out {
    /// Matrix group `g`'s output, live.
    Group(usize),
    /// The lift slot's output, live when either input is.
    Passenger(usize),
    /// Jagged group `g`'s output.
    Jagged(usize),
    /// Zeros.
    Dead,
}

/// The native side of a lift or head: the children's tapes, the fold's groups and recorded tape,
/// and how the block is published.
struct HeadNative<'p> {
    ta: Option<HeadTape<'p>>,
    tb: HeadTape<'p>,
    layout: HeadLayout,
    ft: FoldTape,
    ties: Vec<Vec<Tie>>,
    jties: Vec<Vec<JTie>>,
    outs: Vec<(Entry, Out)>,
    lc_groups: Option<[usize; 2]>,
    spread_w: usize,
    /// Whether the previous head slot is routed as staying whatever its key, with the routing
    /// gadget's advice forged to match.
    forge: bool,
}

/// A child's fresh claims, in the order the fold reads them.
struct Fresh {
    bool_: Vec<(MatrixClaim, MatrixClaim)>,
    el: Vec<(MatrixClaim, MatrixClaim)>,
    sigma: Vec<MatrixClaim>,
    jagged: Vec<JaggedClaim>,
}

fn fresh(t: &HeadTape<'_>, key: &EnvKey) -> Fresh {
    let union = UnionInstance::new(&key.shape.registry, key.shape.counts.clone());
    Fresh {
        bool_: t.mat_assert.claims(&key.shape.registry),
        el: t.el_assert.claims(&union),
        sigma: t.sigma_native.claims(),
        jagged: t.jag.claims().into_iter().cloned().collect(),
    }
}

type Widths = (usize, Vec<(usize, usize)>, (usize, usize), (usize, usize));

fn widths(f: &Fresh) -> Widths {
    let wid = |c: &MatrixClaim| (c.col.n_vars(), c.row.n_vars());
    let mut g = Vec::new();
    for (a, b) in f.bool_.iter().chain(&f.el) {
        g.push(wid(a));
        g.push(wid(b));
    }
    let k_row = f
        .jagged
        .iter()
        .find_map(|c| match &c.row {
            JaggedRowWeight::Eq(_, p) => Some(p.len()),
            JaggedRowWeight::Combo(_) => None,
        })
        .expect("an eq jagged claim");
    (
        f.bool_.len(),
        g,
        wid(&f.sigma[0]),
        (f.jagged[0].col.len(), k_row),
    )
}

/// Every table type of a circuit's registry: its column count and its two matrices, Boolean
/// types first; and the number of Boolean types.
type TableMats<'k> = (Vec<(usize, &'k dyn FoldMatrix, &'k dyn FoldMatrix)>, usize);

fn table_mats(key: &EnvKey) -> TableMats<'_> {
    let registry = &key.shape.registry;
    let mut v: Vec<(usize, &dyn FoldMatrix, &dyn FoldMatrix)> = Vec::new();
    for (t, (a, b)) in key.boolean_mats().into_iter().enumerate() {
        v.push((
            1usize << registry.boolean_types()[t].k_log,
            a as &dyn FoldMatrix,
            b as &dyn FoldMatrix,
        ));
    }
    let n_bool = v.len();
    for s in registry.element_types() {
        let et = s.element_type().expect("an element slot's table");
        let (a, b) = (et.a_0(), et.b_0());
        v.push((a.num_cols, a as &dyn FoldMatrix, b as &dyn FoldMatrix));
    }
    (v, n_bool)
}

fn is_dead(q: &MatrixClaim) -> bool {
    q.row.low.iter().all(|x| *x == F128::ZERO)
}

/// The circuit-structure matrix of `circuit` and each claim's column marginal, one pass per
/// distinct live row weight.
fn sigma_marginals<'c>(
    circuit: &'c flock_core::circuit::Circuit,
    cs: &[MatrixClaim],
) -> (
    flock_core::circuit::CircuitStructureMatrix<'c>,
    Vec<Vec<F128>>,
) {
    let m = SigmaAssertion::matrix(circuit);
    let n_cols = FoldMatrix::n_cols(&m);
    let mut rows: Vec<Option<usize>> = Vec::with_capacity(cs.len());
    let mut distinct: Vec<Vec<F128>> = Vec::new();
    for (i, q) in cs.iter().enumerate() {
        if is_dead(q) {
            rows.push(None);
            continue;
        }
        match cs[..i]
            .iter()
            .zip(&rows)
            .find_map(|(p, r)| (p.row == q.row).then_some(*r).flatten())
        {
            Some(j) => rows.push(Some(j)),
            None => {
                rows.push(Some(distinct.len()));
                distinct.push(q.row.materialize());
            }
        }
    }
    let ms = if distinct.is_empty() {
        Vec::new()
    } else {
        m.col_marginals(&distinct)
    };
    let combs: Vec<Vec<F128>> = rows
        .iter()
        .map(|r| match r {
            Some(j) => ms[*j].clone(),
            None => vec![F128::ZERO; n_cols],
        })
        .collect();
    (m, combs)
}

#[allow(clippy::too_many_arguments)]
fn head_native<'p>(
    los: &'p [LeafOuter],
    a: Option<&HeadChild<'p>>,
    b: &HeadChild<'p>,
    lift: Option<&EnvKey>,
    mats: [&dyn FoldMatrix; 2],
    lc: [(usize, usize); 2],
    env: &HeadEnv,
    forge: bool,
    timings: &mut HeadTimings,
) -> HeadNative<'p> {
    let t0 = Instant::now();
    let (ta, tb) = match a {
        Some(a) => {
            let (ta, tb) = rayon::join(
                || HeadTape::new(&los[0], ENV_DOMAIN, a.outer, a.whir),
                || HeadTape::new(&los[1], ENV_DOMAIN, b.outer, b.whir),
            );
            (Some(ta), tb)
        }
        None => (None, HeadTape::new(&los[0], ENV_DOMAIN, b.outer, b.whir)),
    };
    timings.tapes = t0.elapsed().as_secs_f64();
    let t0 = Instant::now();
    let fb = fresh(&tb, b.key);
    let fa = ta.as_ref().map(|t| fresh(t, a.unwrap().key));
    let (n_wrap_bool, wrap, sigma_wrap, jagged_wrap) = widths(&fb);
    let env_head = env.layout.clone().unwrap_or_default();
    let (n_head_bool, head, sigma_head, jagged_head) = match &fa {
        Some(f) => widths(f),
        None => (
            env_head.n_head_bool,
            env_head.head.clone(),
            env_head.sigma_head,
            env_head.jagged_head,
        ),
    };
    let layout = HeadLayout {
        lc,
        n_wrap_bool,
        wrap,
        n_head_bool,
        head,
        sigma_wrap,
        sigma_head,
        jagged_wrap,
        jagged_head,
    };
    let has_a = a.is_some();
    let a_entry = |e: Entry| -> Option<usize> {
        let a = a?;
        let (at, w) = a.layout?.find(e)?;
        (w == layout.locate(e).1).then_some(a.block + at)
    };
    let prior = |e: Entry, low: Low| match a_entry(e) {
        Some(at) => Tie::Entry { at, low },
        None => Tie::Dead,
    };
    let mut ties: Vec<Vec<Tie>> = Vec::new();
    let mut jties: Vec<Vec<JTie>> = Vec::new();
    let mut outs: Vec<(Entry, Out)> = Vec::new();
    let mut groups_of: Vec<(usize, usize)> = Vec::new();
    for t in 0..layout.wrap.len() / 2 {
        for side in 0..2 {
            let g = 2 * t + side;
            let fresh_b = if t < n_wrap_bool {
                Tie::Bool {
                    kid: Kid::B,
                    t,
                    side,
                }
            } else {
                Tie::El {
                    kid: Kid::B,
                    t: t - n_wrap_bool,
                    side,
                }
            };
            let mut v = Vec::new();
            if has_a {
                v.push(prior(Entry::Wrap(g), Low::Live));
            }
            v.push(fresh_b);
            outs.push((Entry::Wrap(g), Out::Group(ties.len())));
            groups_of.push(layout.wrap[g]);
            ties.push(v);
        }
    }
    for t in 0..layout.head.len() / 2 {
        for side in 0..2 {
            let g = 2 * t + side;
            if !has_a {
                outs.push((Entry::Head(g), Out::Dead));
                continue;
            }
            let fresh_a = if t < n_head_bool {
                Tie::Bool {
                    kid: Kid::A,
                    t,
                    side,
                }
            } else {
                Tie::El {
                    kid: Kid::A,
                    t: t - n_head_bool,
                    side,
                }
            };
            outs.push((Entry::Head(g), Out::Group(ties.len())));
            groups_of.push(layout.head[g]);
            ties.push(vec![prior(Entry::Head(g), Low::Live), fresh_a]);
        }
    }
    let mut v = Vec::new();
    if has_a {
        v.push(prior(Entry::SigmaWrap, Low::Live));
    }
    v.extend((0..fb.sigma.len()).map(|j| Tie::Sigma { kid: Kid::B, j }));
    outs.push((Entry::SigmaWrap, Out::Group(ties.len())));
    groups_of.push(layout.sigma_wrap);
    ties.push(v);
    if has_a {
        outs.push((Entry::SigmaLift, Out::Passenger(ties.len())));
        groups_of.push(layout.sigma_head);
        ties.push(vec![
            prior(Entry::SigmaLift, Low::Live),
            prior(Entry::SigmaHead, Low::Move),
        ]);
        let mut v = vec![prior(Entry::SigmaHead, Low::Stay)];
        v.extend((0..fa.as_ref().unwrap().sigma.len()).map(|j| Tie::Sigma { kid: Kid::A, j }));
        outs.push((Entry::SigmaHead, Out::Group(ties.len())));
        groups_of.push(layout.sigma_head);
        ties.push(v);
    } else {
        outs.push((Entry::SigmaLift, Out::Dead));
        outs.push((Entry::SigmaHead, Out::Dead));
    }
    let lc_groups = a.map(|a| {
        let al = a.layout.expect("a head child's layout");
        let g = [ties.len(), ties.len() + 1];
        for i in 0..2 {
            groups_of.push(lc[i]);
            ties.push(vec![
                Tie::Lc {
                    kid: Kid::A,
                    at: a.block + al.lc_at(i),
                },
                Tie::Lc {
                    kid: Kid::B,
                    at: b.block + layout.lc_at(i),
                },
            ]);
        }
        g
    });
    let jprior = |e: Entry| match a_entry(e) {
        Some(at) => JTie::Entry { at },
        None => JTie::Dead,
    };
    let mut v = Vec::new();
    if has_a {
        v.push(jprior(Entry::JaggedWrap));
    }
    v.push(JTie::Fresh { kid: Kid::B });
    outs.push((Entry::JaggedWrap, Out::Jagged(0)));
    jties.push(v);
    if has_a {
        outs.push((Entry::JaggedHead, Out::Jagged(1)));
        jties.push(vec![jprior(Entry::JaggedHead), JTie::Fresh { kid: Kid::A }]);
    } else {
        outs.push((Entry::JaggedHead, Out::Dead));
    }

    // The native claims, routing and folds.
    let pa: &[F128] = a.map(|a| &a.proof.public[..]).unwrap_or(&[]);
    let get = |i: usize| pa.get(i).copied().unwrap_or(F128::ZERO);
    let cd_b = digest_f128(&b.key.digest());
    let (stay, mov) = match a {
        Some(a) => {
            let kat = a.block + layout.keys_at();
            let k = |j: usize| [get(kat + 2 * j), get(kat + 2 * j + 1)];
            let live = |e: Entry| a_entry(e).is_some_and(|at| get(at) != F128::ZERO);
            if live(Entry::SigmaWrap) {
                assert_eq!(k(0), cd_b, "the previous wrap slot names the wrap circuit");
            }
            let cd_a = digest_f128(&a.key.digest());
            let l2 = live(Entry::SigmaHead);
            let (stay, mov) = if forge {
                (l2, false)
            } else {
                (l2 && k(2) == cd_a, l2 && k(2) != cd_a)
            };
            if mov && live(Entry::SigmaLift) {
                assert_eq!(k(1), k(2), "two lift entries name one circuit");
            }
            (stay, mov)
        }
        None => (false, false),
    };
    let kid_fresh = |kid: Kid| {
        if kid == Kid::A {
            fa.as_ref().unwrap()
        } else {
            &fb
        }
    };
    let kid_pub = |kid: Kid| match kid {
        Kid::A => &a.unwrap().proof.public[..],
        Kid::B => &b.proof.public[..],
    };
    let claim_of = |tie: &Tie, w: (usize, usize)| -> MatrixClaim {
        match *tie {
            Tie::Entry { at, low } => {
                let c = read_entry(pa, at, w.0, w.1);
                match low {
                    Low::Live => c,
                    Low::Stay => super::node::gate_claim(&c, stay),
                    Low::Move => super::node::gate_claim(&c, mov),
                }
            }
            Tie::Dead => dead(w.0, w.1),
            Tie::Lc { kid, at } => read_lc(kid_pub(kid), at, w.0, w.1),
            Tie::Bool { kid, t, side } => {
                let p = &kid_fresh(kid).bool_[t];
                if side == 0 { p.0.clone() } else { p.1.clone() }
            }
            Tie::El { kid, t, side } => {
                let p = &kid_fresh(kid).el[t];
                if side == 0 { p.0.clone() } else { p.1.clone() }
            }
            Tie::Sigma { kid, j } => kid_fresh(kid).sigma[j].clone(),
        }
    };
    let claims: Vec<Vec<MatrixClaim>> = ties
        .iter()
        .zip(&groups_of)
        .map(|(ts, &w)| ts.iter().map(|t| claim_of(t, w)).collect())
        .collect();
    let grinding = FoldGrinding::per_challenge_128();
    let mut rec = RecordingChallenger::new(FsChallenger::with_chained_blake3(HEAD_FOLD_DOMAIN));
    let mut proofs: Vec<FoldProof> = Vec::new();
    let mut folded: Vec<MatrixClaim> = Vec::new();
    let mut fold = |m: &dyn FoldMatrix, combs: Vec<Vec<F128>>, cs: &[MatrixClaim], rec: &mut _| {
        let (fp, out) = prove_fold_with_grinding(m, &combs, cs, grinding, rec);
        proofs.push(fp);
        folded.push(out);
    };
    let marginals = |m: &dyn FoldMatrix, n_cols: usize, cs: &[MatrixClaim]| -> Vec<Vec<F128>> {
        cs.iter()
            .map(|q| {
                if is_dead(q) {
                    vec![F128::ZERO; n_cols]
                } else {
                    m.col_marginal(&q.row.materialize(), n_cols)
                }
            })
            .collect()
    };
    let mut table_groups: Vec<(&EnvKey, usize)> = vec![(b.key, layout.wrap.len())];
    if let Some(a) = a {
        table_groups.push((a.key, layout.head.len()));
    }
    let mut g = 0usize;
    for (key, n_groups) in table_groups {
        let (tm, n_bool) = table_mats(key);
        let lcs = key.boolean_lcs();
        let bm = key.boolean_mats();
        for (t, &(n_cols, ma, mb)) in tm.iter().enumerate().take(n_groups / 2) {
            let (ca, cb) = (&claims[g], &claims[g + 1]);
            let (xa, xb) = if t < n_bool {
                let mut xa = Vec::new();
                let mut xb = Vec::new();
                for (qa, qb) in ca.iter().zip(cb) {
                    let (x, y) = if is_dead(qa) && is_dead(qb) {
                        (vec![F128::ZERO; n_cols], vec![F128::ZERO; n_cols])
                    } else if qa.row == qb.row {
                        lcs[t].fold_split(&qa.row.materialize())
                    } else {
                        (
                            col_marginal(bm[t].0, &qa.row.materialize(), n_cols),
                            col_marginal(bm[t].1, &qb.row.materialize(), n_cols),
                        )
                    };
                    xa.push(x);
                    xb.push(y);
                }
                (xa, xb)
            } else {
                (marginals(ma, n_cols, ca), marginals(mb, n_cols, cb))
            };
            fold(ma, xa, ca, &mut rec);
            fold(mb, xb, cb, &mut rec);
            g += 2;
        }
    }
    let (m, combs) = sigma_marginals(&b.key.shape.circuit, &claims[g]);
    fold(&m, combs, &claims[g], &mut rec);
    g += 1;
    if let Some(a) = a {
        let lift = lift.expect("a head names the lift circuit");
        let (m, combs) = sigma_marginals(&lift.shape.circuit, &claims[g]);
        fold(&m, combs, &claims[g], &mut rec);
        let (m, combs) = sigma_marginals(&a.key.shape.circuit, &claims[g + 1]);
        fold(&m, combs, &claims[g + 1], &mut rec);
        g += 2;
        for (i, m) in mats.iter().enumerate() {
            let cs = &claims[g + i];
            let combs = cs
                .iter()
                .map(|q| m.col_marginal(&q.row.materialize(), m.n_cols()))
                .collect();
            fold(*m, combs, cs, &mut rec);
        }
        g += 2;
    }
    assert_eq!(g, ties.len(), "every group folded");
    let jparams = |key: &EnvKey| {
        let u = UnionInstance::new(&key.shape.registry, key.shape.counts.clone());
        JaggedParams::from_heights(&u.jagged_heights(), u.n_log(), key.pcs.m - LOG_PACKING)
    };
    let mut jkeys: Vec<([u8; 32], Vec<JaggedClaim>)> = Vec::new();
    let mut jproofs = Vec::new();
    let mut jfolded = Vec::new();
    for (gi, jt) in jties.iter().enumerate() {
        let (key, w) = if gi == 0 {
            (b.key, layout.jagged_wrap)
        } else {
            (a.unwrap().key, layout.jagged_head)
        };
        let mut cs: Vec<JaggedClaim> = Vec::new();
        for t in jt {
            match *t {
                JTie::Entry { at } => cs.push(
                    JaggedClaim::from_folded(&read_entry(pa, at, w.0, w.1))
                        .expect("a published jagged entry"),
                ),
                JTie::Dead => cs.push(
                    JaggedClaim::from_folded(&dead(w.0, w.1)).expect("the zero jagged claim"),
                ),
                JTie::Fresh { kid } => cs.extend(kid_fresh(kid).jagged.iter().cloned()),
            }
        }
        rec.observe_label(b"flock-aggregate-jagged-v0");
        rec.observe_bytes(&key.digest());
        let (jfp, jout) = prove_fold_jagged_with_grinding(
            &JaggedTable::from_params(&jparams(key)),
            &cs,
            grinding,
            &mut rec,
        );
        jkeys.push((key.digest(), cs));
        jproofs.push(jfp);
        jfolded.push(jout);
    }
    let ft = FoldTape::located(
        rec,
        HEAD_FOLD_DOMAIN,
        &claims,
        &proofs,
        folded,
        &jkeys,
        &jproofs,
        jfolded,
    );
    timings.fold = t0.elapsed().as_secs_f64();
    let mut spread_w = tb.spread_w.max(b.key.shape.circuit.cells().mu());
    if let Some(ta) = &ta {
        spread_w = spread_w
            .max(ta.spread_w)
            .max(a.unwrap().key.shape.circuit.cells().mu());
    }
    HeadNative {
        ta,
        tb,
        layout,
        ft,
        ties,
        jties,
        outs,
        lc_groups,
        spread_w,
        forge,
    }
}

/// `1` when `a = b` word for word, else `0`, with the inverse as advice.
#[allow(clippy::too_many_arguments)]
fn emit_is_eq(
    sb: &mut ShapeBuilder,
    macs: flock_core::circuit::builder::SlotId,
    k: Consts,
    a: [Wire; 2],
    b: [Wire; 2],
    native: ([F128; 2], [F128; 2]),
    forge: bool,
    vals: &mut Vec<F128>,
) -> Wire {
    let (zw, ow) = (k.zw, k.ow);
    let mut m = ow;
    for j in 0..2 {
        let d = native.0[j] + native.1[j];
        let d_w = sb.gate(macs, &[a[j], b[j], ow])[0];
        vals.push(if d == F128::ZERO || forge {
            F128::ZERO
        } else {
            d.inv()
        });
        let inv_w = sb.input();
        let p_w = sb.gate(macs, &[zw, d_w, inv_w])[0];
        let z_w = sb.gate(macs, &[ow, p_w, ow])[0];
        let chk = sb.gate(macs, &[zw, z_w, d_w])[0];
        sb.connect(chk, k.zassert);
        m = sb.gate(macs, &[zw, m, z_w])[0];
    }
    m
}

/// What one emission of a lift or head circuit hands back.
struct HeadBuild {
    eb: EnvBuild,
    need: usize,
    census: EnvCensus,
    block: usize,
}

fn emit_head(
    hn: &HeadNative<'_>,
    a: Option<&HeadChild<'_>>,
    b: &HeadChild<'_>,
    env: &HeadEnv,
    nu: usize,
    spread_decl: usize,
) -> HeadBuild {
    let mut eb = EnvBuild::begin(env, nu, spread_decl);
    let k = eb.k;
    let (zw, ow) = (k.zw, k.ow);
    let fixed = eb.fixed.clone();
    let lay = &hn.layout;
    let ft = &hn.ft;
    let mut ground: Vec<(Wire, Wire)> = Vec::new();
    let block = {
        let EnvBuild {
            sb,
            cs,
            vals,
            hints,
            consts,
            ..
        } = &mut eb;
        let macs_b = crate::tower::envelope::slot_cached(sb, &mut cs.resid, 603, MacGate::new);
        let b3_b = cs.q.b3_alt.expect("the second BLAKE3 slot");
        let ra: Option<HeadRegion> = hn.ta.as_ref().map(|t| {
            let isl = sb.begin_island();
            let r = emit_head_region(sb, cs, cs.q.b3, t, k, vals, hints, consts);
            sb.end_island(isl);
            r
        });
        let rb = {
            let saved = cs.macs;
            cs.macs = macs_b;
            cs.resid
                .iter_mut()
                .filter(|e| e.0 == 600)
                .for_each(|e| e.1 = macs_b);
            let isl = sb.begin_island();
            let r = emit_head_region(sb, cs, b3_b, &hn.tb, k, vals, hints, consts);
            sb.end_island(isl);
            cs.macs = saved;
            cs.resid
                .iter_mut()
                .filter(|e| e.0 == 600)
                .for_each(|e| e.1 = saved);
            r
        };
        let macs = cs.macs;
        if !env.measure
            && let (Some(r), Some(t)) = (&ra, &hn.ta)
        {
            for (i, &w) in fixed.iter().enumerate() {
                ground.push((r.child_pub_w[i], w));
            }
            for (p, ws) in r.bind_w.iter().enumerate() {
                for (&w, v) in ws.iter().zip(payload_values(t, p)) {
                    let c = cw(sb, vals, consts, v);
                    emit_assert_eq(sb, macs, k, w, c);
                }
            }
        }
        for (i, f) in b.key.shape.circuit.fixed_public().iter().enumerate() {
            if let Some(v) = *f {
                let c = cw(sb, vals, consts, v);
                emit_assert_eq(sb, macs, k, rb.child_pub_w[i], c);
            }
        }
        for (p, ws) in rb.bind_w.iter().enumerate() {
            for (&w, v) in ws.iter().zip(payload_values(&hn.tb, p)) {
                let c = cw(sb, vals, consts, v);
                emit_assert_eq(sb, macs, k, w, c);
            }
        }
        let fe: FoldEmit = emit_folds(sb, cs, k, ft, vals, consts);
        let lam_w: Vec<Wire> = PHI_8_TABLE[..1 << K_SKIP]
            .iter()
            .map(|&v| cw(sb, vals, consts, v))
            .collect();
        let deninv_w = cw(sb, vals, consts, subspace_denominator_pair(K_SKIP).1);
        let lows_of = |t: &HeadTape<'_>,
                       r: &HeadRegion,
                       sb: &mut ShapeBuilder,
                       vals: &mut Vec<F128>|
         -> Vec<Wire> {
            match (&t.zskip, &r.zskip) {
                (ZskipTapeRec::Rs { ch, .. }, ZskipWires::Rs(zskip_w)) => emit_lagrange_lows(
                    sb,
                    macs,
                    &lam_w,
                    deninv_w,
                    *zskip_w,
                    t.chals[*ch],
                    vals,
                    zw,
                    ow,
                    k.zassert,
                ),
                _ => panic!("lifts, heads and wraps run the RS zerocheck"),
            }
        };
        let lows_b = lows_of(&hn.tb, &rb, sb, vals);
        let lows_a = match (&hn.ta, &ra) {
            (Some(t), Some(r)) => lows_of(t, r, sb, vals),
            _ => Vec::new(),
        };
        let pa_len = a.map(|a| a.proof.public.len()).unwrap_or(0);
        let cpa = |i: usize| match &ra {
            Some(r) if i < pa_len => r.child_pub_w[i],
            _ => zw,
        };
        let get = |i: usize| {
            a.and_then(|a| a.proof.public.get(i).copied())
                .unwrap_or(F128::ZERO)
        };
        let region = |kid: Kid| {
            if kid == Kid::A {
                ra.as_ref().unwrap()
            } else {
                &rb
            }
        };
        let tape = |kid: Kid| {
            if kid == Kid::A {
                hn.ta.as_ref().unwrap()
            } else {
                &hn.tb
            }
        };
        let cd_a = ra.as_ref().map(|r| r.cd_w).unwrap_or([zw, zw]);
        // The previous head slot's routing, and the lift slot's key and liveness.
        let (stay_w, move_w, k1_out, live1_out) = match a {
            Some(a) => {
                let kat = a.block + lay.keys_at();
                let kw = |j: usize| [cpa(kat + 2 * j), cpa(kat + 2 * j + 1)];
                let kn = |j: usize| [get(kat + 2 * j), get(kat + 2 * j + 1)];
                let live_w = |e: Entry| match a.layout.and_then(|al| al.find(e)) {
                    Some((at, w)) if w == lay.locate(e).1 => cpa(a.block + at),
                    _ => zw,
                };
                let (l0, l1, l2) = (
                    live_w(Entry::SigmaWrap),
                    live_w(Entry::SigmaLift),
                    live_w(Entry::SigmaHead),
                );
                for j in 0..2 {
                    let d = sb.gate(macs, &[kw(0)[j], rb.cd_w[j], ow])[0];
                    let t = sb.gate(macs, &[zw, l0, d])[0];
                    sb.connect(t, k.zassert);
                }
                let m2 = emit_is_eq(
                    sb,
                    macs,
                    k,
                    kw(2),
                    cd_a,
                    (kn(2), digest_f128(&a.key.digest())),
                    hn.forge,
                    vals,
                );
                let stay = sb.gate(macs, &[zw, l2, m2])[0];
                let mov = sb.gate(macs, &[l2, stay, ow])[0];
                let both = sb.gate(macs, &[zw, l1, mov])[0];
                let mut k1 = [zw; 2];
                for j in 0..2 {
                    let d = sb.gate(macs, &[kw(1)[j], kw(2)[j], ow])[0];
                    let t = sb.gate(macs, &[zw, both, d])[0];
                    sb.connect(t, k.zassert);
                    k1[j] = sb.gate(macs, &[kw(1)[j], mov, d])[0];
                }
                let lm = sb.gate(macs, &[l1, mov, ow])[0];
                let live1 = sb.gate(macs, &[lm, l1, mov])[0];
                (stay, mov, k1, live1)
            }
            None => (zw, zw, [zw, zw], zw),
        };
        let mut gated: Vec<((Low, usize), Wire)> = Vec::new();
        for (gi, ts) in hn.ties.iter().enumerate() {
            let loc = &ft.locs[gi];
            let (kc, kr) = (loc.k_col, loc.k_row);
            for (ci, tie) in ts.iter().enumerate() {
                let cl = &loc.claims[ci];
                let pts = |sb: &mut ShapeBuilder,
                           col: &dyn Fn(usize) -> Wire,
                           row: &dyn Fn(usize) -> Wire| {
                    for j in 0..cl.col_pt_n {
                        sb.connect(fe.wv(cl.col_pt_v + j), col(j));
                    }
                    for j in 0..cl.row_pt_n {
                        sb.connect(fe.wv(cl.row_pt_v + j), row(j));
                    }
                };
                match *tie {
                    Tie::Entry { at, low } => {
                        assert_eq!((cl.row_low_n, cl.col_low_n), (1, 1));
                        let v = cpa(at + 1 + kc + kr);
                        let (lw, vw) = match low {
                            Low::Live => (cpa(at), v),
                            Low::Stay | Low::Move => {
                                let gw = if low == Low::Stay { stay_w } else { move_w };
                                let gv = match gated.iter().find(|(k2, _)| *k2 == (low, at)) {
                                    Some(&(_, gv)) => gv,
                                    None => {
                                        let gv = sb.gate(macs, &[zw, gw, v])[0];
                                        gated.push(((low, at), gv));
                                        gv
                                    }
                                };
                                (gw, gv)
                            }
                        };
                        sb.connect(fe.wv(cl.row_low_v), lw);
                        sb.connect(fe.wv(cl.col_low_v), lw);
                        pts(sb, &|j| cpa(at + 1 + j), &|j| cpa(at + 1 + kc + j));
                        sb.connect(fe.wv(cl.value_v), vw);
                    }
                    Tie::Dead => {
                        for j in 0..cl.row_low_n {
                            sb.connect(fe.wv(cl.row_low_v + j), zw);
                        }
                        for j in 0..cl.col_low_n {
                            sb.connect(fe.wv(cl.col_low_v + j), zw);
                        }
                        pts(sb, &|_| zw, &|_| zw);
                        sb.connect(fe.wv(cl.value_v), zw);
                    }
                    Tie::Lc { kid, at } => {
                        let r = region(kid);
                        let len = if kid == Kid::A {
                            pa_len
                        } else {
                            b.proof.public.len()
                        };
                        let cp = |x: usize| if x < len { r.child_pub_w[x] } else { zw };
                        sb.connect(fe.wv(cl.row_low_v), ow);
                        sb.connect(fe.wv(cl.col_low_v), ow);
                        pts(sb, &|j| cp(at + j), &|j| cp(at + kc + j));
                        sb.connect(fe.wv(cl.value_v), cp(at + kc + kr));
                    }
                    Tie::Bool { kid, t, side } => {
                        let (r, tk) = (region(kid), tape(kid));
                        let lows = if kid == Kid::A { &lows_a } else { &lows_b };
                        let n_lc = r.b_lc_w.len();
                        pts(sb, &|j| r.b_lc_w[n_lc - 1 - j], &|j| {
                            r.b_mlv_w[if j == 0 { 0 } else { tk.n_log_i + j }]
                        });
                        for j in 0..cl.col_low_n {
                            sb.connect(fe.wv(cl.col_low_v + j), r.b_zpartial_w[j]);
                        }
                        for (j, &lw) in lows.iter().enumerate().take(cl.row_low_n) {
                            sb.connect(fe.wv(cl.row_low_v + j), lw);
                        }
                        let ev = r.mat_eval_w[t];
                        sb.connect(fe.wv(cl.value_v), if side == 0 { ev.0 } else { ev.1 });
                    }
                    Tie::El { kid, t, side } => {
                        let (r, tk) = (region(kid), tape(kid));
                        sb.connect(fe.wv(cl.row_low_v), ow);
                        sb.connect(fe.wv(cl.col_low_v), ow);
                        let n_lc = r.el_lc_rho_w.len();
                        pts(sb, &|j| r.el_lc_rho_w[n_lc - 1 - j], &|j| {
                            r.el_zc_rho_w[tk.n_log_i + j]
                        });
                        let ev = r.el_eval_w[t];
                        sb.connect(fe.wv(cl.value_v), if side == 0 { ev.0 } else { ev.1 });
                    }
                    Tie::Sigma { kid, j } => {
                        let (row_w, col_w, value_w) = &region(kid).structure_claim_w[j];
                        sb.connect(fe.wv(cl.row_low_v), ow);
                        sb.connect(fe.wv(cl.col_low_v), ow);
                        assert_eq!((cl.row_pt_n, cl.col_pt_n), (row_w.len(), col_w.len()));
                        pts(sb, &|x| col_w[x], &|x| row_w[x]);
                        sb.connect(fe.wv(cl.value_v), *value_w);
                    }
                }
            }
        }
        for (gi, jt) in hn.jties.iter().enumerate() {
            let loc = &ft.jlocs[gi];
            let mut ci = 0usize;
            for t in jt {
                match *t {
                    JTie::Entry { .. } | JTie::Dead => {
                        let w = |x: usize| match *t {
                            JTie::Entry { at } => cpa(at + x),
                            _ => zw,
                        };
                        let cl = &loc.claims[ci];
                        let tg = cw(sb, vals, consts, F128::new(0, cl.row_pt.1 as u64));
                        sb.connect(fe.wv(cl.row_scale_v - 1), tg);
                        sb.connect(fe.wv(cl.row_scale_v), w(0));
                        for j in 0..loc.n_col {
                            sb.connect(fe.wv(cl.col_v + j), w(1 + j));
                        }
                        for j in 0..cl.row_pt.1 {
                            sb.connect(fe.wv(cl.row_pt.0 + j), w(1 + loc.n_col + j));
                        }
                        sb.connect(fe.wv(cl.val_v), w(1 + loc.n_col + loc.k_row));
                        ci += 1;
                    }
                    JTie::Fresh { kid } => {
                        let rk = region(kid);
                        for (li, &jw) in rk.jag_w.iter().enumerate() {
                            let cl = &loc.claims[ci];
                            sb.connect(fe.wv(cl.val_v), jw);
                            for j in 0..loc.n_col {
                                sb.connect(fe.wv(cl.col_v + j), rk.jag_sig_w[j]);
                            }
                            if cl.terms.is_empty() {
                                let tg = cw(sb, vals, consts, F128::new(0, cl.row_pt.1 as u64));
                                sb.connect(fe.wv(cl.row_scale_v - 1), tg);
                                sb.connect(fe.wv(cl.row_scale_v), ow);
                                for j in 0..cl.row_pt.1 {
                                    sb.connect(fe.wv(cl.row_pt.0 + j), rk.jag_row_w[li][j]);
                                }
                            } else {
                                let tg = cw(sb, vals, consts, F128::new(1, cl.terms.len() as u64));
                                sb.connect(fe.wv(cl.terms[0].0 - 1), tg);
                                for (tj, &(cv, addr)) in cl.terms.iter().enumerate() {
                                    sb.connect(fe.wv(cv), rk.jag_row_w[li][tj]);
                                    let aw = cw(sb, vals, consts, F128::new(addr as u64, 0));
                                    sb.connect(fe.wv(cv + 1), aw);
                                }
                            }
                            ci += 1;
                        }
                    }
                }
            }
            assert_eq!(ci, loc.claims.len(), "every jagged claim connected");
            let hw = cw(
                sb,
                vals,
                consts,
                F128::new(loc.k_row as u64, loc.claims.len() as u64),
            );
            sb.connect(fe.wv(loc.hdr_v), hw);
            let kw = if gi == 0 { rb.cd_w } else { cd_a };
            for (&w, &c) in fe.payload(ft, ft.jag_payloads[gi]).iter().zip(&kw) {
                sb.connect(w, c);
            }
        }
        let bb = b.block;
        let h_b = [rb.child_pub_w[bb], rb.child_pub_w[bb + 1]];
        let h = match a {
            Some(a) => {
                let h_a = [cpa(a.block), cpa(a.block + 1)];
                emit_parent(sb, cs.q.b3, h_a, h_b, vals, consts)
            }
            None => h_b,
        };
        let mut block = vec![h[0], h[1]];
        for i in 0..2 {
            match hn.lc_groups {
                Some(lg) => {
                    let (rc, rr, v) = &fe.groups[lg[i]];
                    block.extend_from_slice(rc);
                    block.extend_from_slice(rr);
                    block.push(*v);
                }
                None => {
                    let (kc, kr) = lay.lc[i];
                    let at = bb + lay.lc_at(i);
                    block.extend((0..kc + kr + 1).map(|j| rb.child_pub_w[at + j]));
                }
            }
        }
        block.extend_from_slice(&rb.cd_w);
        block.extend_from_slice(&k1_out);
        block.extend_from_slice(&cd_a);
        for (e, (kc, kr)) in lay.entries() {
            let &(_, out) = hn
                .outs
                .iter()
                .find(|(x, _)| *x == e)
                .expect("every entry published");
            match out {
                Out::Group(gi) | Out::Passenger(gi) => {
                    let (rc, rr, v) = &fe.groups[gi];
                    let passenger = matches!(out, Out::Passenger(_));
                    block.push(if passenger { live1_out } else { ow });
                    block.extend_from_slice(rc);
                    block.extend_from_slice(rr);
                    block.push(if passenger {
                        sb.gate(macs, &[zw, live1_out, *v])[0]
                    } else {
                        *v
                    });
                }
                Out::Jagged(gi) => {
                    let jp = &fe.jagged[gi];
                    block.push(jp.live);
                    block.extend_from_slice(&jp.rho_col);
                    block.extend_from_slice(&jp.rho_row);
                    block.push(jp.value);
                }
                Out::Dead => block.extend(std::iter::repeat_n(zw, kc + kr + 2)),
            }
        }
        assert_eq!(block.len(), lay.len(), "the head block's layout");
        block
    };
    let need = slot_list(&eb.cs)
        .iter()
        .map(|&(_, s)| eb.sb.rows_in_slot(s))
        .max()
        .unwrap_or(0);
    let mut census = eb.finish(env, &block, hn.spread_w, &ground);
    if a.is_some() {
        census.layout = Some(hn.layout.clone());
    }
    let block_base = if env.measure { census.body } else { env.body };
    HeadBuild {
        eb,
        need,
        census,
        block: block_base,
    }
}

/// Proves a lift over the wrap `b` (when `a` is `None`) or a head over the lift or head `a` and the
/// wrap `b`, in one union-circuit proof built to `env` and opened through `outer`. `lift` is the
/// lift circuit's key (for a head), `mats` the block's lincheck matrices and `lc` their
/// accumulators' column and row variables.
#[allow(clippy::too_many_arguments)]
pub fn prove_head(
    a: Option<&HeadChild<'_>>,
    b: &HeadChild<'_>,
    lift: Option<&EnvKey>,
    mats: [&dyn FoldMatrix; 2],
    lc: [(usize, usize); 2],
    env: &HeadEnv,
    outer: &dyn OuterPcs,
) -> (HeadKey, HeadProof, HeadTimings) {
    prove_head_with(a, b, lift, mats, lc, env, outer, false)
}

/// [`prove_head`] as a forger would run it, routing the previous head slot as staying whatever its
/// key and forging the routing gadget's advice to match; the proof must not verify.
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn prove_head_forging_route(
    a: Option<&HeadChild<'_>>,
    b: &HeadChild<'_>,
    lift: Option<&EnvKey>,
    mats: [&dyn FoldMatrix; 2],
    lc: [(usize, usize); 2],
    env: &HeadEnv,
    outer: &dyn OuterPcs,
) -> (HeadKey, HeadProof, HeadTimings) {
    prove_head_with(a, b, lift, mats, lc, env, outer, true)
}

#[allow(clippy::too_many_arguments)]
fn prove_head_with(
    a: Option<&HeadChild<'_>>,
    b: &HeadChild<'_>,
    lift: Option<&EnvKey>,
    mats: [&dyn FoldMatrix; 2],
    lc: [(usize, usize); 2],
    env: &HeadEnv,
    outer: &dyn OuterPcs,
    forge: bool,
) -> (HeadKey, HeadProof, HeadTimings) {
    let mut timings = HeadTimings::default();
    let los: Vec<LeafOuter> = a
        .iter()
        .map(|a| a.key.leaf_outer(a.proof))
        .chain(std::iter::once(b.key.leaf_outer(b.proof)))
        .collect();
    let hn = head_native(&los, a, b, lift, mats, lc, env, forge, &mut timings);
    let t0 = Instant::now();
    let (nu, sw) = if env.measure {
        let hb = emit_head(&hn, a, b, env, 24, hn.spread_w);
        let nu = (hb.need.next_power_of_two().trailing_zeros() as usize).max(7);
        (nu, hn.spread_w)
    } else {
        if let Some(a) = a {
            assert_eq!(a.block, env.body, "a head child built to the envelope");
        }
        (env.nu, env.spread_w.max(hn.spread_w))
    };
    let HeadBuild {
        eb, census, block, ..
    } = emit_head(&hn, a, b, env, nu, sw);
    let t_emit = t0.elapsed().as_secs_f64();
    let (key, proof, tm) = prove_env(eb, nu, sw, Some(outer), |_| {});
    timings.build = t_emit + tm.build;
    timings.witness = tm.witness;
    timings.prove = tm.prove;
    (
        HeadKey {
            key,
            layout: hn.layout,
            block,
            census,
        },
        proof,
        timings,
    )
}

/// Why a lift or head proof was refused.
#[derive(Debug)]
pub enum HeadVerifyError {
    /// The circuit proof did not verify.
    Proof(FlockVerifyError),
    /// A wiring key names another circuit than its slot's.
    Key,
    /// An accumulated claim does not hold against its table.
    Discharge(&'static str),
}

/// What a verified lift or head states: its chain value and the two lincheck accumulators left for
/// the block's matrices.
pub struct HeadStatement {
    /// The chain value.
    pub h: [F128; 2],
    /// The lincheck accumulators on the block's `A` and `B`.
    pub lc: [MatrixClaim; 2],
}

fn element_mats(k: &EnvKey) -> Vec<ElementMatrices<'_>> {
    k.shape
        .registry
        .element_types()
        .iter()
        .map(|s| s.element_type().expect("an element slot's table"))
        .map(|t| (t.a_0(), t.b_0()))
        .collect()
}

/// Verifies a lift or head proof under `key`: the circuit proof, then every wrap, lift and head
/// accumulator against its table, with `wrap`, `lift` and `head` the three circuits' keys; returns
/// the chain value and the lincheck accumulators.
pub fn verify_head(
    key: &HeadKey,
    wrap: &EnvKey,
    lift: &EnvKey,
    head: &EnvKey,
    proof: &HeadProof,
    outer: &dyn OuterPcs,
) -> Result<HeadStatement, HeadVerifyError> {
    key.key
        .verify(proof, Some(outer))
        .map_err(HeadVerifyError::Proof)?;
    let lay = &key.layout;
    let p = &proof.public;
    let b = key.block;
    let word = |i: usize| [p[b + i], p[b + i + 1]];
    let (wd, ld, hd) = (wrap.digest(), lift.digest(), head.digest());
    let entry = |e: Entry| {
        let (at, (kc, kr)) = lay.locate(e);
        read_entry(p, b + at, kc, kr)
    };
    let live = |c: &MatrixClaim| c.row.low[0] != F128::ZERO;
    let ka = lay.keys_at();
    if word(ka) != digest_f128(&wd) {
        return Err(HeadVerifyError::Key);
    }
    let mut sigma = vec![(wd, entry(Entry::SigmaWrap))];
    let s1 = entry(Entry::SigmaLift);
    if live(&s1) {
        if word(ka + 2) != digest_f128(&ld) {
            return Err(HeadVerifyError::Key);
        }
        sigma.push((ld, s1));
    }
    let s2 = entry(Entry::SigmaHead);
    if live(&s2) {
        let k2 = word(ka + 4);
        let d = [ld, hd]
            .into_iter()
            .find(|d| digest_f128(d) == k2)
            .ok_or(HeadVerifyError::Key)?;
        sigma.push((d, s2));
    }
    let pairs = |n: usize, f: &dyn Fn(usize) -> Entry| -> Vec<(MatrixClaim, MatrixClaim)> {
        (0..n / 2)
            .map(|t| (entry(f(2 * t)), entry(f(2 * t + 1))))
            .collect()
    };
    let jparams = |k: &EnvKey| {
        let u = UnionInstance::new(&k.shape.registry, k.shape.counts.clone());
        JaggedParams::from_heights(&u.jagged_heights(), u.n_log(), k.pcs.m - LOG_PACKING)
    };
    let wrap_pairs = pairs(lay.wrap.len(), &Entry::Wrap);
    let wacc = Accumulator {
        registry_digest: wrap.shape.registry.digest(),
        per_type: wrap_pairs[..lay.n_wrap_bool].to_vec(),
        per_element: wrap_pairs[lay.n_wrap_bool..].to_vec(),
        sigma: Vec::new(),
        jagged: vec![(wd, entry(Entry::JaggedWrap))],
    };
    if !wacc.discharge(&wrap.boolean_mats()) || !wacc.discharge_element(&element_mats(wrap)) {
        return Err(HeadVerifyError::Discharge("a wrap table"));
    }
    if !wacc.discharge_jagged(&[(wd, &jparams(wrap))]) {
        return Err(HeadVerifyError::Discharge("the wrap layout"));
    }
    let head_pairs = pairs(lay.head.len(), &Entry::Head);
    let je = entry(Entry::JaggedHead);
    let hacc = Accumulator {
        registry_digest: key.key.shape.registry.digest(),
        per_type: head_pairs[..lay.n_head_bool].to_vec(),
        per_element: head_pairs[lay.n_head_bool..].to_vec(),
        sigma,
        jagged: if live(&je) {
            vec![(hd, je)]
        } else {
            Vec::new()
        },
    };
    if !hacc.discharge(&key.key.boolean_mats()) || !hacc.discharge_element(&element_mats(&key.key))
    {
        return Err(HeadVerifyError::Discharge("a head table"));
    }
    if !hacc.discharge_sigma(&[
        &wrap.shape.circuit,
        &lift.shape.circuit,
        &head.shape.circuit,
    ]) {
        return Err(HeadVerifyError::Discharge("a wiring table"));
    }
    if !hacc.discharge_jagged(&[(hd, &jparams(&key.key))]) {
        return Err(HeadVerifyError::Discharge("the head layout"));
    }
    let lc = [0, 1].map(|i| {
        let (kc, kr) = lay.lc[i];
        read_lc(p, b + lay.lc_at(i), kc, kr)
    });
    Ok(HeadStatement { h: word(0), lc })
}

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::{Consts, F128, MacGate, ShapeBuilder, Wire, emit_is_eq};

    /// Runs the key-equality gadget on `a` and `b`, with forged advice when `forge`; returns its
    /// output, or `None` when the witness breaks the circuit.
    fn is_eq(a: [F128; 2], b: [F128; 2], forge: bool) -> Option<F128> {
        catch_unwind(AssertUnwindSafe(|| {
            let mut sb = ShapeBuilder::new(7);
            let macs = sb.slot(MacGate::new());
            let mut vals = Vec::new();
            let k = Consts::new(&mut sb, &mut vals);
            let mut input = |v: F128| -> Wire {
                vals.push(v);
                sb.input()
            };
            let aw = [input(a[0]), input(a[1])];
            let bw = [input(b[0]), input(b[1])];
            let m = emit_is_eq(&mut sb, macs, k, aw, bw, (a, b), forge, &mut vals);
            sb.publish(m);
            let shape = sb.finish().expect("the gadget's circuit builds");
            let w = shape.run(&vals, &[]);
            *w.public.last().expect("the published output")
        }))
        .ok()
    }

    #[test]
    fn the_key_equality_gadget_cannot_be_forged() {
        let x = [F128::new(3, 5), F128::new(7, 11)];
        let y = [F128::new(3, 5), F128::new(7, 12)];
        let z = [F128::new(4, 5), F128::new(7, 11)];
        assert_eq!(is_eq(x, x, false), Some(F128::ONE), "equal keys");
        assert_eq!(
            is_eq(x, y, false),
            Some(F128::ZERO),
            "keys differing in the second word"
        );
        assert_eq!(
            is_eq(x, z, false),
            Some(F128::ZERO),
            "keys differing in the first word"
        );
        assert_eq!(is_eq(x, y, true), None, "forged equality, second word");
        assert_eq!(is_eq(x, z, true), None, "forged equality, first word");
        assert_eq!(
            is_eq(x, x, true),
            Some(F128::ONE),
            "equal keys need no advice"
        );
    }
}
