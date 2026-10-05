// Added to the vendored copy of Flock; see VENDORED.md at the vendored root.
//! The in-circuit verifier of a row-major Flock proof opened through the merged transport, and the
//! wrap that proves many of them in one union-circuit proof.
//!
//! A row-major child is a proof of `prove_fast_core`'s zerocheck and lincheck over one Boolean
//! block, whose two ring-switched claims and one packed-direct claim are opened through
//! `open_batch_merged` on a single full-height column. Its transcript runs on chained BLAKE3.
//!
//! The circuit replays the child's whole transcript as BLAKE3 compressions and arithmetises:
//! every grinding check; the zerocheck's round-one interpolations, rounds and final product; the
//! lincheck's rounds; both ring-switch claim checks; the merged opening's family-H relation,
//! multipoint intake and anchor expect; and Ligerito's query phase (with the per-query weights
//! derived in-circuit from the transcript), sumcheck spine and residual. The lincheck's final
//! equation, which evaluates the block's constraint matrices, and the packed-direct claim's value,
//! which is a function of the application statement, are published for the wrap's verifier.

use std::any::Any;

use flock_core::{
    circuit::builder::SlotId,
    field::F256,
    lincheck::{SkipPoint, build_eq_table},
    matrix_fold::{
        FoldGrinding, FoldMatrix, FoldProof, JaggedAssertion, MatrixClaim,
        prove_fold_with_grinding_owned,
    },
    pcs::{
        Commitment, MergedOpenProof, OuterPcs, PcsParams,
        jagged::{JaggedParams, assist_boundaries},
    },
    proof::ZClaim,
    zerocheck::{
        K_SKIP,
        multilinear::subspace_denominator_pair,
        univariate_skip_optimized::{medium_challenges_ghash, small_challenges_ghash},
    },
};
use flock_field::phi8::PHI_8_TABLE;
use flock_multilinear::{IndexOrder, eq_table};
use flock_transcript::transcript_record::{
    RecordingChallenger, Stream, StreamWord, TranscriptOp as Op,
};

use crate::{
    r1cs_hashes::fs_chain::{FsChainTrace, IV},
    tower::{
        CollapsedSlots, F128, FsChallenger, HashKind, InnerPd, LeafEvalGate256, Lvl, MpRec,
        OpenLevel, PdRec, RoundRec, SLOT_WORDS, ShapeBuilder, Wire, cap_payloads, cap_wires,
        child_walker::ChildSlots,
        cw, emit_fiat_shamir_chain, emit_recorded_pow_checks, emit_residual_region, flatten_ops,
        gates_spine::emit_mac256,
        head_env::{
            ENV_DOMAIN, EnvBuild, EnvCensus, EnvKey, EnvProof, HeadEnv, prove_env, slot_list,
        },
        level_geometry, level_sources, pack8, parse_open_levels,
        query::emit_opening,
        query_phase_blake3_rows, replay_ligerito_spine256, squeeze_word_wire, strat_scheds,
        walker_common::{
            self, LBL_FROBENIUS, LBL_LINCHECK, LBL_MERGED_OPEN, LBL_MULTIPOINT, LBL_RING_SWITCH,
            LBL_ZEROCHECK, RS_SHAT_WORDS, Z_PARTIAL_WORDS, prefix_product,
        },
    },
};

/// One row-major child proof and the transcript its native verification recorded.
pub struct RowMajorChild<'p> {
    /// The recording challenger after the child's full verification.
    pub rec: RecordingChallenger<FsChallenger>,
    /// The child's transcript domain.
    pub domain: Vec<u8>,
    /// The child's merged opening.
    pub opening: &'p MergedOpenProof,
    /// The child's witness commitment.
    pub commitment: &'p Commitment,
    /// The child's commitment parameters.
    pub pcs: PcsParams,
    /// The lincheck's opened claim.
    pub ab: ZClaim,
    /// The zerocheck's opened claim.
    pub c: ZClaim,
    /// The packed-direct claim's point on the committed words.
    pub pd_point: Vec<F128>,
    /// The published words of every row, whose digest the transcript absorbs and whose
    /// multilinear extension the packed-direct claim opens.
    pub rows: Vec<Vec<F128>>,
    /// The lincheck's final running claim.
    pub lc_running: F128,
    /// The lincheck's two matrix claims, on `A` then `B`: row weight `λ(z) ⊗ eq(x)`, column weight
    /// `z_partial ⊗ eq(rr)`.
    pub lc_claims: [MatrixClaim; 2],
    /// The block's constant-pin column.
    pub konst: usize,
    /// The merged opening's layout claims.
    pub jagged: JaggedAssertion,
    /// The block's R1CS digest, to which the circuit holds the one the transcript absorbs.
    pub r1cs_digest: [u8; 32],
}

/// Where a transcript squeeze landed: its finalisation ordinal and its challenge ordinal.
#[derive(Clone, Copy, Debug)]
struct Sq {
    fin: usize,
    ch: usize,
}

/// One sumcheck round: its messages' value ordinal and its challenge.
#[derive(Clone, Copy, Debug)]
struct Round {
    g_v: usize,
    sq: Sq,
}

/// The row-major PIOP located on a child's tape.
struct PiopRec {
    r_outer: (usize, usize),
    r1_ab_v: usize,
    r1_c_v: usize,
    z: Sq,
    zc_rounds: Vec<Round>,
    finals_v: usize,
    alpha: Sq,
    beta: Sq,
    lc_rounds: Vec<Round>,
    zp_v: usize,
    inner_skip: Sq,
    io: Vec<Sq>,
    digest_payload: usize,
    r1cs_payload: usize,
}

/// One recorded row-major child verification, parsed: every region located and every native replica
/// the emitter and the self-check consume.
pub(super) struct RowMajorTape<'p> {
    child: &'p RowMajorChild<'p>,
    vals_rec: Vec<F128>,
    chals: Vec<F128>,
    ops: Vec<Op>,
    pub_payloads: Vec<bool>,
    cap_pays: Vec<usize>,
    trace: FsChainTrace,
    stream: Stream,
    bytes: Vec<u8>,
    cross: Vec<Option<(usize, usize)>>,
    pub(super) b3_rows: usize,
    pub(super) spread_w: usize,
    piop: PiopRec,
    start_v: usize,
    gammas_o: Vec<PdRec>,
    w_rounds: Vec<RoundRec>,
    w_resid: Vec<RoundRec>,
    mp_o: MpRec,
    inner_pd2: InnerPd,
    yr_v2: usize,
    yr_len: usize,
    levels: Vec<OpenLevel>,
    lvl_src: Vec<(&'p [[u8; 32]], &'p Vec<Vec<F128>>, &'p Vec<[u8; 32]>)>,
    geo: Vec<Lvl>,
    native_sums: Vec<F256>,
    rs_recs: Vec<(usize, usize, usize)>,
    rs_gam_fins: Vec<(usize, usize)>,
    t_final_n: F256,
    anc_end_n: F128,
    n_log_i: usize,
    m_mp2: usize,
    run_consts: Vec<(F128, u64, u64)>,
    x_ab_n: Vec<F128>,
    x_c_n: Vec<F128>,
}

/// The value ordinal and challenge ordinal at an op index.
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

/// The finalisation ordinal of the op at an index.
fn fin_at(ops: &[Op], end: usize) -> usize {
    ops[..end].iter().filter(|o| o.finalizes()).count()
}

/// The byte-payload ordinal of the op at an index.
fn payload_at(ops: &[Op], end: usize) -> usize {
    ops[..end].iter().filter(|o| o.carries_payload()).count()
}

struct Cursor<'a> {
    ops: &'a [Op],
    i: usize,
}

impl Cursor<'_> {
    fn skip_pows(&mut self) {
        while matches!(self.ops[self.i], Op::Pow { .. }) {
            self.i += 1;
        }
    }

    fn label(&mut self, l: &[u8]) {
        assert!(
            matches!(&self.ops[self.i], Op::Label(x) if x.as_slice() == l),
            "expected label {}, got {:?}",
            String::from_utf8_lossy(l),
            self.ops[self.i]
        );
        self.i += 1;
    }

    fn scalar(&mut self) -> Sq {
        self.skip_pows();
        assert!(
            matches!(self.ops[self.i], Op::SqueezeScalar),
            "expected a scalar squeeze, got {:?}",
            self.ops[self.i]
        );
        let sq = Sq {
            fin: fin_at(self.ops, self.i),
            ch: vc_at(self.ops, self.i).1,
        };
        self.i += 1;
        sq
    }

    fn slice(&mut self, n: usize) -> (usize, usize) {
        self.skip_pows();
        assert!(
            matches!(self.ops[self.i], Op::SqueezeSlice(k) if k == n),
            "expected a {n}-slice squeeze, got {:?}",
            self.ops[self.i]
        );
        let at = (fin_at(self.ops, self.i), vc_at(self.ops, self.i).1);
        self.i += 1;
        at
    }

    fn observe_slice(&mut self, n: usize) -> usize {
        assert!(
            matches!(self.ops[self.i], Op::ObserveSlice(k) if k == n),
            "expected a {n}-slice observe, got {:?}",
            self.ops[self.i]
        );
        let v = vc_at(self.ops, self.i).0;
        self.i += 1;
        v
    }

    fn observe_bytes(&mut self, n: usize) -> usize {
        assert!(
            matches!(self.ops[self.i], Op::ObserveBytes(k) if k == n),
            "expected {n} observed bytes, got {:?}",
            self.ops[self.i]
        );
        let p = payload_at(self.ops, self.i);
        self.i += 1;
        p
    }

    /// The sumcheck rounds that follow: two observed scalars, then a (ground) scalar squeeze.
    fn rounds(&mut self) -> Vec<Round> {
        let mut out = Vec::new();
        while matches!(self.ops[self.i], Op::ObserveScalar)
            && matches!(self.ops[self.i + 1], Op::ObserveScalar)
        {
            let mut j = self.i + 2;
            while matches!(self.ops[j], Op::Pow { .. }) {
                j += 1;
            }
            if !matches!(self.ops[j], Op::SqueezeScalar) {
                break;
            }
            let g_v = vc_at(self.ops, self.i).0;
            self.i = j;
            out.push(Round {
                g_v,
                sq: self.scalar(),
            });
        }
        out
    }
}

impl<'p> RowMajorTape<'p> {
    pub(super) fn new(child: &'p RowMajorChild<'p>) -> Self {
        let rec = &child.rec;
        let t_shape = rec.shape();
        let chals: Vec<F128> = rec.challenges().to_vec();
        let vals_rec: Vec<F128> = rec.values().to_vec();
        let ops: Vec<Op> = flatten_ops(t_shape.ops()).to_vec();
        let find = |label: &[u8]| -> Vec<usize> {
            ops.iter()
                .enumerate()
                .filter_map(|(i, op)| {
                    matches!(op, Op::Label(l) if l.as_slice() == label).then_some(i)
                })
                .collect()
        };
        let (zc_l, lc_l, mo_l, rs_l, mp_l, fa_l) = (
            find(LBL_ZEROCHECK),
            find(LBL_LINCHECK),
            find(LBL_MERGED_OPEN),
            find(LBL_RING_SWITCH),
            find(LBL_MULTIPOINT),
            find(LBL_FROBENIUS),
        );
        assert_eq!(zc_l.len(), 1, "one zerocheck");
        assert_eq!(lc_l.len(), 1, "one lincheck");
        assert_eq!(mo_l.len(), 1, "one merged open");
        assert_eq!(rs_l.len(), 2, "two ring-switched claims");
        assert_eq!(mp_l.len(), 1, "one multipoint region");
        assert_eq!(fa_l.len(), 1, "one anchor region");
        assert!(zc_l[0] < lc_l[0] && lc_l[0] < mo_l[0] && mo_l[0] < rs_l[0]);

        // ---- the statement head: the published words' digest, then the r1cs binding ----
        let mut cur = Cursor { ops: &ops, i: 0 };
        assert!(
            matches!(&ops[0], Op::Label(_)),
            "the statement label opens the tape"
        );
        cur.i = 1;
        let digest_payload = cur.observe_bytes(32);
        assert!(
            matches!(&ops[cur.i], Op::Label(_)),
            "the r1cs binding label"
        );
        cur.i += 1;
        let r1cs_payload = cur.observe_bytes(32);
        let cap_bytes = 32 * child.commitment.cap.len();
        cur.observe_bytes(cap_bytes);
        assert_eq!(cur.i, zc_l[0], "the zerocheck follows the binding");

        // ---- the zerocheck ----
        cur.label(LBL_ZEROCHECK);
        let m = child.pcs.m;
        let n_outer = m - K_SKIP - 7;
        cur.slice(K_SKIP);
        let r_outer = cur.slice(n_outer);
        let r1_ab_v = cur.observe_slice(1 << K_SKIP);
        let r1_c_v = cur.observe_slice(1 << K_SKIP);
        let z = cur.scalar();
        let zc_rounds = cur.rounds();
        assert_eq!(
            zc_rounds.len(),
            m - K_SKIP,
            "one zerocheck round per multilinear variable"
        );
        let finals_v = vc_at(&ops, cur.i).0;
        for _ in 0..2 {
            assert!(matches!(ops[cur.i], Op::ObserveScalar), "zerocheck finals");
            cur.i += 1;
        }

        // ---- the lincheck ----
        cur.label(LBL_LINCHECK);
        let alpha = cur.scalar();
        let beta = cur.scalar();
        let lc_rounds = cur.rounds();
        let zp_v = cur.observe_slice(Z_PARTIAL_WORDS);
        let inner_skip = cur.scalar();
        let mut io = Vec::new();
        while cur.i < mo_l[0] {
            io.push(cur.scalar());
        }
        let piop = PiopRec {
            r_outer,
            r1_ab_v,
            r1_c_v,
            z,
            zc_rounds,
            finals_v,
            alpha,
            beta,
            lc_rounds,
            zp_v,
            inner_skip,
            io,
            digest_payload,
            r1cs_payload,
        };

        // ---- the merged open: two ring switches, the packed-direct value, one coefficient vector ----
        cur.label(LBL_MERGED_OPEN);
        let mut rs_recs = Vec::new();
        for k in 0..2 {
            cur.label(LBL_RING_SWITCH);
            let sv = cur.observe_slice(RS_SHAT_WORDS);
            assert_eq!(
                &vals_rec[sv..sv + RS_SHAT_WORDS],
                &child.opening.ring_switches[k].s_hat_v[..],
                "s_hat_v {k} on the stream"
            );
            let (fin, ch) = cur.slice(7);
            rs_recs.push((sv, fin, ch));
        }
        let mut pd_recs = Vec::new();
        while matches!(ops[cur.i], Op::ObserveScalar) {
            pd_recs.push(vc_at(&ops, cur.i).0);
            cur.i += 1;
        }
        assert_eq!(
            pd_recs.len(),
            1,
            "one packed-direct claim: the published words"
        );
        let (rs_gam_fin, rs_gam_ch) = cur.slice(2 + pd_recs.len());
        let rs_gam_fins = vec![(rs_gam_fin, 0), (rs_gam_fin, 1)];

        // ---- the chain, the open phase and the geometry ----
        let mc = walker_common::merge_and_replay_chain(
            &t_shape,
            &child.domain,
            rec.values(),
            rec.payloads(),
            &ops,
            &chals,
        );
        let lig = &child.opening.inner.ligerito_opening().ligerito;
        assert_eq!(
            child.commitment.cap, lig.initial_cap,
            "the commitment is the L0 cap"
        );
        let r_lvl = lig.recursive_caps.len();
        let lvl_src = level_sources(lig);
        let (start_v, piop_o, gammas_o, w_rounds, mp_o, inner_pd2, yr_v2, levels) =
            parse_open_levels(&ops, 32 * lig.initial_cap.len(), r_lvl);
        assert!(piop_o.is_none(), "a row-major child has no element PIOP");
        assert_eq!(
            gammas_o.len(),
            1,
            "the parser sees the one packed-direct claim"
        );
        assert_eq!(
            gammas_o[0].val_v, pd_recs[0],
            "the packed-direct value is the absorbed one"
        );
        assert_eq!(
            w_rounds.len(),
            child.opening.merged_rounds.len(),
            "the W rounds fill the dense domain"
        );
        let (geo, native_sums) = level_geometry(
            &levels,
            &lvl_src,
            &chals,
            HashKind::Blake3,
            &strat_scheds(&child.pcs),
        );
        let b3_rows = mc.trace.rows.len() + query_phase_blake3_rows(&geo);
        let spread_w = geo.iter().map(|g| g.depth).max().unwrap().max(1);
        let cap_pays = cap_payloads(&mc.stream, &mc.bytes, &lvl_src);
        let pub_payloads = vec![false; payload_at(&ops, ops.len())];

        // ---- the natives: the intake, the spine, the anchor ----
        let fro = &child.opening.frobenius;
        {
            use flock_core::pcs::ring_switch::{
                build_fold_byte_table, inner_product, linearized_coefficients,
                tensor_algebra_transpose,
            };
            use flock_core::zerocheck::univariate_skip::build_eq;
            let gs: Vec<F128> = (0..2).map(|k| chals[rs_gam_ch + k]).collect();
            let mut target = F128::ZERO;
            let mut coeffs: Vec<Vec<F128>> = Vec::new();
            for (k, &(sv, _, rc)) in rs_recs.iter().enumerate() {
                let shv = &vals_rec[sv..sv + RS_SHAT_WORDS];
                let rdp: Vec<F128> = (0..7).map(|j| chals[rc + j]).collect();
                let eq = build_eq(&rdp);
                target += gs[k] * inner_product(&tensor_algebra_transpose(shv), &eq);
                let scaled: Vec<F128> = eq.iter().map(|x| gs[k] * *x).collect();
                coeffs.push(linearized_coefficients(&build_fold_byte_table(&scaled)));
            }
            for pd in &gammas_o {
                target += chals[pd.ch] * vals_rec[pd.val_v];
            }
            let mut running = target;
            for rr in &w_rounds {
                let (g1, gi) = (vals_rec[rr.g_v], vals_rec[rr.g_v + 1]);
                let r = chals[rr.ch];
                let g0 = running + g1;
                running = g0 + (g1 + g0 + gi) * r + gi * r * r;
            }
            let mut big_v = F128::ZERO;
            for (k, cs) in coeffs.iter().enumerate() {
                for (j, &cj) in cs.iter().enumerate() {
                    if cj.is_zero() {
                        continue;
                    }
                    let mut x = fro.values[k][j];
                    for _ in 0..j {
                        x = x * x;
                    }
                    big_v += cj * x;
                }
            }
            for &v in &fro.group_values {
                big_v += v;
            }
            assert_eq!(
                running,
                vals_rec[inner_pd2.q_v] * big_v,
                "the merged boundary replays"
            );
        }
        let t_final_n = replay_ligerito_spine256(
            &levels,
            &vals_rec,
            &chals,
            start_v,
            chals[inner_pd2.ch] * vals_rec[inner_pd2.q_v],
            &native_sums,
        );
        let anc_end_n = walker_common::parse_anchor_native_endpoint(&vals_rec, &chals, &mp_o);

        // ---- the anchor geometry: one full-height column ----
        let n_log_i = m - 7;
        let m_mp2 = mp_o.rounds.len();
        assert_eq!(w_rounds.len(), m_mp2, "merged rho spans the dense domain");
        assert_eq!(m_mp2, n_log_i, "the dense domain is the committed words");
        let params_i = JaggedParams::from_heights(&[1u64 << n_log_i], n_log_i, m_mp2);
        let bounds = assist_boundaries(&params_i);
        let run_consts: Vec<(F128, u64, u64)> = bounds
            .iter()
            .map(|&(t_c, t_next, len)| (F128::new(u64::from(len & 1), 0), t_c, t_next))
            .collect();
        let x_full =
            |z: &ZClaim| [z.point.x_inner_rest.as_slice(), z.point.x_outer.as_slice()].concat();
        let (x_ab_n, x_c_n) = (x_full(&child.ab), x_full(&child.c));
        assert_eq!(x_ab_n.len(), 1 + n_log_i, "ab point split");
        assert_eq!(x_c_n.len(), 1 + n_log_i, "c point split");
        assert_eq!(child.pd_point.len(), n_log_i, "pd point split");
        {
            let sig_n: Vec<F128> = mp_o.anchor_rounds.iter().map(|rr| chals[rr.ch]).collect();
            let w_n = run_w_native(&run_consts, &sig_n, m_mp2);
            for (si, c) in child.jagged.rs.iter().enumerate() {
                assert_eq!(c.value, w_n, "RS raw W {si} is the single-column constant");
            }
            for (combo, dense) in &child.jagged.groups {
                let mut raw = combo.as_ref().map_or(F128::ZERO, |c| c.value);
                for (g, c) in dense {
                    raw += *g * c.value;
                }
                let g = chals[gammas_o[0].ch];
                assert_eq!(
                    raw,
                    g * w_n,
                    "the group's raw W is the single-column constant"
                );
            }
        }
        let yr_len = lig.final_proof.yr.len() / 2;
        let w_resid = if geo[0].row_words < geo[0].lanes {
            let k_rot = w_rounds.len() - levels[0].fold_fins.len();
            let mut v = w_rounds[k_rot..].to_vec();
            v.extend_from_slice(&w_rounds[..k_rot]);
            v
        } else {
            w_rounds.clone()
        };
        RowMajorTape {
            child,
            vals_rec,
            chals,
            ops,
            pub_payloads,
            cap_pays,
            trace: mc.trace,
            stream: mc.stream,
            bytes: mc.bytes,
            cross: mc.cross,
            b3_rows,
            spread_w,
            piop,
            start_v,
            gammas_o,
            w_rounds,
            w_resid,
            mp_o,
            inner_pd2,
            yr_v2,
            yr_len,
            levels,
            lvl_src,
            geo,
            native_sums,
            rs_recs,
            rs_gam_fins,
            t_final_n,
            anc_end_n,
            n_log_i,
            m_mp2,
            run_consts,
            x_ab_n,
            x_c_n,
        }
    }
}

/// The layout weight of a single-column stack at the anchor's round challenges `sig`.
fn run_w_native(runs: &[(F128, u64, u64)], sig: &[F128], m_mp2: usize) -> F128 {
    let bit = |b: bool| if b { F128::ONE } else { F128::ZERO };
    runs.iter().fold(F128::ZERO, |acc, &(w, t_c, t_next)| {
        let mut p = F128::ONE;
        for l in 0..=m_mp2 {
            p *= F128::ONE + sig[2 * l] + bit((t_c >> l) & 1 == 1);
            p *= F128::ONE + sig[2 * l + 1] + bit((t_next >> l) & 1 == 1);
        }
        acc + w * p
    })
}

/// The wires of a chunk's two lincheck matrix claims, which the wrap's fold absorbs.
pub(super) struct FoldSurface {
    pub(super) row_low: Vec<Wire>,
    pub(super) row_pt: Vec<Wire>,
    pub(super) col_low: Vec<Wire>,
    pub(super) col_pt: Vec<Wire>,
    pub(super) values: [Wire; 2],
}

/// One named block of a region's published tail.
pub(super) struct Tail {
    pub(super) name: &'static str,
    pub(super) wires: Vec<Wire>,
}

/// The shared constant and assert-zero wires every region uses.
#[derive(Clone, Copy)]
pub(super) struct Consts {
    pub(super) zw: Wire,
    pub(super) ow: Wire,
    pub(super) zassert: Wire,
}

impl Consts {
    pub(super) fn new(sb: &mut ShapeBuilder, vals: &mut Vec<F128>) -> Consts {
        vals.extend_from_slice(&[F128::ZERO, F128::ONE, F128::ZERO]);
        Consts {
            zw: sb.fixed_public_input(F128::ZERO),
            ow: sb.fixed_public_input(F128::ONE),
            zassert: sb.fixed_public_input(F128::ZERO),
        }
    }
}

/// Lagrange weights at `z` on `nodes`, `L_i(z) = Z(z)·den⁻¹·(z + node_i)⁻¹`, with the inverses as
/// advice bound by `(z + node_i)·y_i = 1`; returns the weights, `Z(z)` and the inverses.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_skip_weights(
    sb: &mut ShapeBuilder,
    macs: SlotId,
    nodes: &[F128],
    deninv: F128,
    z_w: Wire,
    z_n: F128,
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
    k: Consts,
) -> (Vec<Wire>, Wire, Vec<Wire>) {
    let mut t_w = Vec::with_capacity(nodes.len());
    let mut prod = k.ow;
    for &s in nodes {
        let s_w = cw(sb, vals, consts, s);
        let t = sb.gate(macs, &[z_w, s_w, k.ow])[0];
        prod = sb.gate(macs, &[k.zw, prod, t])[0];
        t_w.push(t);
    }
    let den_w = cw(sb, vals, consts, deninv);
    let scale = sb.gate(macs, &[k.zw, prod, den_w])[0];
    let mut ys = Vec::with_capacity(nodes.len());
    let weights = nodes
        .iter()
        .zip(&t_w)
        .map(|(&s, &t)| {
            let tn = z_n + s;
            assert!(!tn.is_zero(), "a skip point on a node (≈2^-121)");
            vals.push(tn.inv());
            let y = sb.input();
            let delta = sb.gate(macs, &[k.ow, t, y])[0];
            sb.connect(delta, k.zassert);
            ys.push(y);
            sb.gate(macs, &[k.zw, scale, y])[0]
        })
        .collect();
    (weights, prod, ys)
}

/// `Σ_i a_i·b_i` over wire pairs.
pub(super) fn emit_dot(
    sb: &mut ShapeBuilder,
    macs: SlotId,
    a: &[Wire],
    b: &[Wire],
    k: Consts,
) -> Wire {
    a.iter()
        .zip(b)
        .fold(k.zw, |acc, (&x, &y)| sb.gate(macs, &[acc, x, y])[0])
}

/// The ring-switch claim check `Σ_i L_i·(s_i + x0·(s_i + s_{64+i})) = value`, as a zero delta.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_claim_check(
    sb: &mut ShapeBuilder,
    macs: SlotId,
    skip_w: &[Wire],
    x0: Wire,
    shv: &[Wire],
    value: Wire,
    k: Consts,
) {
    let half = skip_w.len();
    let mut acc = k.zw;
    for i in 0..half {
        let t = sb.gate(macs, &[shv[i], shv[half + i], k.ow])[0];
        let u = sb.gate(macs, &[shv[i], x0, t])[0];
        acc = sb.gate(macs, &[acc, skip_w[i], u])[0];
    }
    let delta = sb.gate(macs, &[acc, value, k.ow])[0];
    sb.connect(delta, k.zassert);
}

/// The eq tensor over F128 coordinate wires, least significant coordinate first.
pub(super) fn emit_eq_tensor(
    sb: &mut ShapeBuilder,
    macs: SlotId,
    coords: &[Wire],
    k: Consts,
) -> Vec<Wire> {
    let mut t = vec![k.ow];
    for &r in coords {
        let old = t;
        let mut next = Vec::with_capacity(2 * old.len());
        for &x in &old {
            next.push(sb.gate(macs, &[x, x, r])[0]);
        }
        for &x in &old {
            next.push(sb.gate(macs, &[k.zw, x, r])[0]);
        }
        t = next;
    }
    t
}

/// The eq tensor over GF(2^256) coordinate wire pairs, least significant coordinate first.
pub(super) fn emit_eq_tensor256(
    sb: &mut ShapeBuilder,
    mac256: SlotId,
    coords: &[[Wire; 2]],
    k: Consts,
) -> Vec<[Wire; 2]> {
    let z2 = [k.zw, k.zw];
    let mut t = vec![[k.ow, k.zw]];
    for &r in coords {
        let old = t;
        let mut next = Vec::with_capacity(2 * old.len());
        for &x in &old {
            next.push(emit_mac256(sb, mac256, x, x, r));
        }
        for &x in &old {
            next.push(emit_mac256(sb, mac256, z2, x, r));
        }
        t = next;
    }
    t
}

/// Ligerito's query phase with every per-query weight derived in-circuit: the query weight
/// `eq(α, k)` from the query-batching squeezes and the lane weight `eq(v_hi, h)` from the fold
/// squeezes. Returns the alpha wires, the level accumulators and the query positions.
#[allow(clippy::too_many_arguments)]
fn emit_query_phase_bound(
    sb: &mut ShapeBuilder,
    slots: CollapsedSlots,
    iv: [Wire; 2],
    leafeval: &[SlotId],
    macs: SlotId,
    mac256: SlotId,
    t: &RowMajorTape<'_>,
    outs: &[Vec<Wire>],
    cap_w: &[Vec<[Wire; 2]>],
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
    hints: &mut Vec<[u32; SLOT_WORDS]>,
    k: Consts,
) -> (Vec<Vec<Wire>>, Vec<[Wire; 2]>, Vec<Vec<Wire>>) {
    use crate::tower::{PARENT, hash_to_digest, pack_params};
    let (trace, chals) = (&t.trace, &t.chals[..]);
    let mut alphas: Vec<Vec<Wire>> = Vec::new();
    let mut level_accs: Vec<[Wire; 2]> = Vec::new();
    let mut query_positions: Vec<Vec<Wire>> = Vec::new();
    for (li, lvl) in t.levels.iter().enumerate() {
        let g = &t.geo[li];
        let (_cap, rows, paths) = t.lvl_src[li];
        let c_min = g.sched.summand_depths.last().copied().unwrap_or(g.c);
        assert!(
            g.c > 0,
            "depth-0 top summand (q = 1) unsupported in-circuit"
        );
        let n_layers = (g.c - c_min).max(1);
        let mut layers_w: Vec<Vec<[Wire; 2]>> = vec![cap_w[li].clone()];
        for _ in 0..n_layers {
            let params = cw(sb, vals, consts, pack_params(0, 64, PARENT));
            let next: Vec<[Wire; 2]> = layers_w
                .last()
                .unwrap()
                .chunks(2)
                .map(|p| {
                    let out = sb.gate(
                        slots.b3,
                        &[iv[0], iv[1], p[0][0], p[0][1], p[1][0], p[1][1], params],
                    );
                    [out[0], out[1]]
                })
                .collect();
            layers_w.push(next);
        }
        let parent_params = cw(sb, vals, consts, pack_params(0, 64, PARENT));
        let a_wires: Vec<Wire> = (0..lvl.a_count)
            .map(|j| squeeze_word_wire(outs, trace, lvl.a_fin, j))
            .collect();
        let v_wires: Vec<[Wire; 2]> = lvl
            .fold_fins
            .iter()
            .map(|&f| {
                [
                    squeeze_word_wire(outs, trace, f, 0),
                    squeeze_word_wire(outs, trace, f, 1),
                ]
            })
            .collect();
        let alpha_vals: Vec<F128> = (0..lvl.a_count).map(|j| chals[lvl.a_ch + j]).collect();
        let aw_n = build_eq_table(&alpha_vals);
        let aw_w = emit_eq_tensor(sb, macs, &a_wires, k);
        let le_vars = g.lanes.min(8).trailing_zeros() as usize;
        let le_groups = g.lanes >> le_vars;
        let v_hi: Vec<F256> = lvl.fold_chs[le_vars..]
            .iter()
            .map(|&i| F256::new(chals[i], chals[i + 1]))
            .collect();
        let hw_n = eq_table(&v_hi, F256::ONE, IndexOrder::LowToHigh);
        let hw_w = emit_eq_tensor256(sb, mac256, &v_wires[le_vars..], k);
        assert!(
            aw_w.len() >= g.q && hw_w.len() == le_groups,
            "the weight tensors cover every query and lane group"
        );
        let zero = cw(sb, vals, consts, F128::ZERO);
        let mut acc = [zero, zero];
        let mut level_positions = Vec::with_capacity(g.q);
        let pad_w = (g.row_words < g.lanes).then_some([zero, zero]);
        for q in 0..g.q {
            vals.extend_from_slice(&rows[q]);
            let leaf_w: Vec<Wire> = (0..g.raw_row_words).map(|_| sb.input()).collect();
            let index_w = squeeze_word_wire(outs, trace, lvl.q_fin, q);
            let (ck, stratum) = g.q_stratum(q);
            let open_depth = g.depth - ck;
            let (cv, position_w) = emit_opening(
                sb,
                slots,
                iv,
                &leaf_w,
                index_w,
                open_depth,
                0,
                stratum << open_depth,
                Some(consts),
                vals,
            );
            level_positions.push(position_w);
            let pos = g.q_pos(q, chals[lvl.q_ch + q].lo);
            hints.extend(g.full_path(q, pos, paths).iter().map(hash_to_digest));
            let (bind, term) = if ck == g.c {
                let sib = cap_w[li][stratum ^ 1];
                let (l, r) = if stratum & 1 == 0 {
                    (cv, sib)
                } else {
                    (sib, cv)
                };
                let out = sb.gate(
                    slots.b3,
                    &[iv[0], iv[1], l[0], l[1], r[0], r[1], parent_params],
                );
                ([out[0], out[1]], layers_w[1][stratum >> 1])
            } else {
                (cv, layers_w[g.c - ck][stratum])
            };
            sb.connect(bind[0], term[0]);
            sb.connect(bind[1], term[1]);
            let mut fold_w: Vec<[Wire; 2]> = leaf_w.iter().map(|&w| [w, zero]).collect();
            fold_w.resize(g.lanes, pad_w.unwrap_or(fold_w[0]));
            let lanes = g.lanes.min(8);
            for h in 0..le_groups {
                let mut a_in: Vec<Wire> = fold_w[lanes * h..lanes * (h + 1)]
                    .iter()
                    .flat_map(|p| *p)
                    .collect();
                a_in.extend(v_wires[..le_vars].iter().flat_map(|p| *p));
                let weight = emit_mac256(sb, mac256, [k.zw, k.zw], hw_w[h], [aw_w[q], k.zw]);
                debug_assert_eq!(hw_n[h] * aw_n[q], hw_n[h] * F256::new(aw_n[q], F128::ZERO));
                a_in.extend_from_slice(&weight);
                a_in.extend_from_slice(&acc);
                let out = sb.gate(leafeval[li], &a_in);
                acc = [out[0], out[1]];
            }
        }
        alphas.push(a_wires);
        level_accs.push(acc);
        query_positions.push(level_positions);
    }
    (alphas, level_accs, query_positions)
}

/// The tape surface of an RS zerocheck: `(fin, ch, len)` of the outer eq slice, the round-one
/// messages' value ordinals, `(fin, ch)` of the skip point, `(g_v, fin, ch)` per round and the
/// finals' value ordinal.
pub(super) struct ZcSurface {
    pub(super) r_outer: (usize, usize, usize),
    pub(super) r1_ab_v: usize,
    pub(super) r1_c_v: usize,
    pub(super) z: (usize, usize),
    pub(super) rounds: Vec<(usize, usize, usize)>,
    pub(super) finals_v: usize,
}

/// What an arithmetised zerocheck hands its consumers: the skip point, its S-node weights, the
/// interpolated `c` claim, the eq point's baked and squeezed coordinates, and the finals.
pub(super) struct ZcWires {
    pub(super) z_w: Wire,
    pub(super) z_n: F128,
    pub(super) skip_c: Vec<Wire>,
    pub(super) c_eval_w: Wire,
    pub(super) c_eval_n: F128,
    pub(super) baked: Vec<F128>,
    pub(super) r_outer_w: Vec<Wire>,
    pub(super) r_outer_n: Vec<F128>,
    pub(super) va_w: Wire,
    pub(super) vb_w: Wire,
}

/// Arithmetises an RS zerocheck in full: round one's Λ and Λ ∪ S interpolations at the skip point,
/// every round, and the final product against the finals.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_rs_zerocheck(
    sb: &mut ShapeBuilder,
    cs: &ChildSlots,
    k: Consts,
    zc: &ZcSurface,
    outs: &[Vec<Wire>],
    trace: &FsChainTrace,
    wv: &impl Fn(usize) -> Wire,
    chals: &[F128],
    vals_rec: &[F128],
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> ZcWires {
    let (zw, ow, zassert) = (k.zw, k.ow, k.zassert);
    let macs = cs.macs;
    let ell = 1usize << K_SKIP;
    let z_w = outs[trace.squeezes[zc.z.0][0]][0];
    let z_n = chals[zc.z.1];
    let s_nodes = &PHI_8_TABLE[..ell];
    let l_nodes = &PHI_8_TABLE[ell..2 * ell];
    let den6 = subspace_denominator_pair(K_SKIP).1;
    let den7 = subspace_denominator_pair(K_SKIP + 1).1;
    let (skip_c, zs_w, _) = emit_skip_weights(sb, macs, s_nodes, den6, z_w, z_n, vals, consts, k);
    let (lam_w, zl_w, yl_w) = emit_skip_weights(sb, macs, l_nodes, den6, z_w, z_n, vals, consts, k);
    let r1_ab: Vec<Wire> = (0..ell).map(|i| wv(zc.r1_ab_v + i)).collect();
    let r1_c: Vec<Wire> = (0..ell).map(|i| wv(zc.r1_c_v + i)).collect();
    let c_eval_w = emit_dot(sb, macs, &lam_w, &r1_c, k);
    let den7_w = cw(sb, vals, consts, den7);
    let zz = sb.gate(macs, &[zw, zs_w, zl_w])[0];
    let scale7 = sb.gate(macs, &[zw, zz, den7_w])[0];
    let mut comb_w = zw;
    for i in 0..ell {
        let wi = sb.gate(macs, &[zw, scale7, yl_w[i]])[0];
        let si = sb.gate(macs, &[r1_ab[i], r1_c[i], ow])[0];
        comb_w = sb.gate(macs, &[comb_w, wi, si])[0];
    }
    let mut run_w = sb.gate(macs, &[comb_w, c_eval_w, ow])[0];
    let (c_eval_n, mut run_n) = {
        use flock_core::zerocheck::multilinear::{
            interpolate_at_z_combined, interpolate_at_z_on_lambda,
        };
        let ab: Vec<F128> = (0..ell).map(|i| vals_rec[zc.r1_ab_v + i]).collect();
        let c: Vec<F128> = (0..ell).map(|i| vals_rec[zc.r1_c_v + i]).collect();
        let comb: Vec<F128> = ab.iter().zip(&c).map(|(&x, &y)| x + y).collect();
        let ce = interpolate_at_z_on_lambda(&c, K_SKIP, z_n);
        (ce, interpolate_at_z_combined(&comb, K_SKIP, z_n) + ce)
    };
    let baked: Vec<F128> = small_challenges_ghash()
        .iter()
        .chain(medium_challenges_ghash().iter())
        .copied()
        .collect();
    let n_outer = zc.r_outer.2;
    let r_outer_w: Vec<Wire> = (0..n_outer)
        .map(|j| squeeze_word_wire(outs, trace, zc.r_outer.0, j))
        .collect();
    let r_outer_n: Vec<F128> = (0..n_outer).map(|j| chals[zc.r_outer.1 + j]).collect();
    let zcr = cs.zcr;
    for (i, &(g_v, fin, ch)) in zc.rounds.iter().enumerate() {
        let (r_eq_n, r_eq_w) = if i < baked.len() {
            (baked[i], cw(sb, vals, consts, baked[i]))
        } else {
            (r_outer_n[i - baked.len()], r_outer_w[i - baked.len()])
        };
        let (g1, gi) = (vals_rec[g_v], vals_rec[g_v + 1]);
        let g0 = (run_n + r_eq_n * g1) * (F128::ONE + r_eq_n).inv();
        vals.push(g0);
        let g0_w = sb.input();
        let rho = chals[ch];
        let o = sb.gate(
            zcr,
            &[
                run_w,
                wv(g_v),
                wv(g_v + 1),
                r_eq_w,
                outs[trace.squeezes[fin][0]][0],
                g0_w,
                ow,
            ],
        );
        sb.connect(o[0], zassert);
        run_w = o[1];
        run_n = g0 * (F128::ONE + rho) + g1 * rho + gi * rho * (F128::ONE + rho);
    }
    let (va_w, vb_w) = (wv(zc.finals_v), wv(zc.finals_v + 1));
    assert_eq!(
        run_n,
        vals_rec[zc.finals_v] * vals_rec[zc.finals_v + 1],
        "the zerocheck closes natively"
    );
    let fin_delta = sb.gate(macs, &[run_w, va_w, vb_w])[0];
    sb.connect(fin_delta, zassert);
    ZcWires {
        z_w,
        z_n,
        skip_c,
        c_eval_w,
        c_eval_n,
        baked,
        r_outer_w,
        r_outer_n,
        va_w,
        vb_w,
    }
}

/// Emits one row-major child's complete verifier region into `sb`, returning its published tail
/// (not yet published) in the order [`check_rowmajor_tail`] walks.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_rowmajor_region(
    sb: &mut ShapeBuilder,
    cs: &mut ChildSlots,
    t: &RowMajorTape<'_>,
    k: Consts,
    vals: &mut Vec<F128>,
    hints: &mut Vec<[u32; SLOT_WORDS]>,
    consts: &mut Vec<(F128, Wire)>,
) -> (Vec<Tail>, FoldSurface) {
    let (trace, stream, chals) = (&t.trace, &t.stream, &t.chals[..]);
    let (zw, ow, zassert) = (k.zw, k.ow, k.zassert);
    let macs = cs.macs;
    let mac256 = cs
        .resid
        .iter()
        .find(|&&(key, _)| key == 701)
        .expect("the F256 MAC slot")
        .1;
    let leafeval: Vec<SlotId> = t
        .geo
        .iter()
        .map(|g| {
            let lanes = g.lanes.min(8);
            match cs.le.iter().find(|(n, _)| *n == 800 + lanes) {
                Some((_, sl)) => *sl,
                None => {
                    let sl = sb.slot(LeafEvalGate256::new(lanes));
                    cs.le.push((800 + lanes, sl));
                    sl
                }
            }
        })
        .collect();
    let iv_w = pack8(&IV);
    let iv2 = [cw(sb, vals, consts, iv_w[0]), cw(sb, vals, consts, iv_w[1])];
    let (outs, ww) = emit_fiat_shamir_chain(
        sb,
        cs.q.b3,
        iv2,
        trace,
        stream,
        &t.bytes,
        vals,
        consts,
        &t.pub_payloads,
        &t.cross,
    );
    emit_recorded_pow_checks(
        sb, cs.q.b3, cs.q.pow, iv2, &t.ops, trace, stream, &outs, &ww, vals, consts,
    );
    let sq_w = |s: Sq| outs[trace.squeezes[s.fin][0]][0];
    let mut vmap: Vec<Option<usize>> = Vec::new();
    for (wi, w) in stream.words.iter().enumerate() {
        if let StreamWord::Value(vi) = *w {
            if vmap.len() <= vi {
                vmap.resize(vi + 1, None);
            }
            vmap[vi] = Some(wi);
        }
    }
    let wv = |vi: usize| -> Wire { ww[vmap[vi].expect("stream word")].expect("wired") };
    let payload_wires = |p: usize| -> Vec<Wire> {
        crate::tower::payload_words(stream)[p]
            .iter()
            .map(|&wi| ww[wi].expect("payload word wired"))
            .collect()
    };

    for (w, v) in payload_wires(t.piop.r1cs_payload)
        .into_iter()
        .zip(super::node::digest_f128(&t.child.r1cs_digest))
    {
        let c = cw(sb, vals, consts, v);
        sb.connect(w, c);
    }

    // ---- Ligerito: the query phase, the multipoint intake, the spine and the residual ----
    let cap_w = cap_wires(stream, &ww, &t.cap_pays);
    let (alphas, level_accs, query_positions) = emit_query_phase_bound(
        sb, cs.q, iv2, &leafeval, macs, mac256, t, &outs, &cap_w, vals, consts, hints, k,
    );
    let (mp_pws, mp_rho2_w, mp_sig_w, anc_w) =
        walker_common::emit_multipoint_intake(sb, cs, trace, &outs, &wv, &t.mp_o, t.m_mp2, zw, ow);
    let t_final = walker_common::emit_ligerito_spine_walk(
        sb,
        cs.spine256,
        &outs,
        trace,
        &wv,
        &t.levels,
        &t.inner_pd2,
        t.start_v,
        &level_accs,
        zw,
        ow,
    );
    let yr_wires: Vec<[Wire; 2]> = (0..t.yr_len)
        .map(|y| [wv(t.yr_v2 + 2 * y), wv(t.yr_v2 + 2 * y + 1)])
        .collect();
    let (_resid_pub, inner_w, (pfslot, pf_w)) = emit_residual_region(
        sb,
        &mut cs.resid,
        &t.levels,
        &t.geo,
        &alphas,
        &query_positions,
        &t.w_resid,
        t.inner_pd2.fin,
        &yr_wires,
        trace,
        &outs,
        zw,
        ow,
    );
    sb.connect(inner_w[0], t_final[0]);
    sb.connect(inner_w[1], t_final[1]);
    let (_tgt_w, _run_w) = walker_common::emit_family_h_boundary(
        sb,
        cs,
        trace,
        &outs,
        &wv,
        &t.rs_recs,
        &t.rs_gam_fins,
        &t.mp_o,
        &t.gammas_o,
        &t.w_rounds,
        &t.inner_pd2,
        pfslot,
        pf_w,
        vals,
        consts,
        zw,
        ow,
    );

    // ---- the zerocheck: round one's interpolations, the rounds and the final product ----
    let p = &t.piop;
    let ell = 1usize << K_SKIP;
    let s_nodes = &PHI_8_TABLE[..ell];
    let den6 = subspace_denominator_pair(K_SKIP).1;
    let zc = emit_rs_zerocheck(
        sb,
        cs,
        k,
        &ZcSurface {
            r_outer: (p.r_outer.0, p.r_outer.1, t.child.pcs.m - K_SKIP - 7),
            r1_ab_v: p.r1_ab_v,
            r1_c_v: p.r1_c_v,
            z: (p.z.fin, p.z.ch),
            rounds: p
                .zc_rounds
                .iter()
                .map(|r| (r.g_v, r.sq.fin, r.sq.ch))
                .collect(),
            finals_v: p.finals_v,
        },
        &outs,
        trace,
        &wv,
        chals,
        &t.vals_rec,
        vals,
        consts,
    );
    let ZcWires {
        z_w,
        z_n,
        skip_c,
        c_eval_w,
        c_eval_n,
        baked,
        r_outer_w,
        r_outer_n,
        va_w,
        vb_w,
    } = zc;

    // ---- the lincheck: its entry and rounds; the final equation is published ----
    let alpha_w = sq_w(p.alpha);
    let beta_w = sq_w(p.beta);
    let lc0 = sb.gate(macs, &[vb_w, alpha_w, va_w])[0];
    let mut lc_w = sb.gate(macs, &[lc0, beta_w, ow])[0];
    for r in &p.lc_rounds {
        lc_w = sb.gate(cs.mrs, &[lc_w, wv(r.g_v), wv(r.g_v + 1), sq_w(r.sq)])[0];
    }
    let zp_w: Vec<Wire> = (0..Z_PARTIAL_WORDS).map(|i| wv(p.zp_v + i)).collect();
    let is_w = sq_w(p.inner_skip);
    let (skip_ab, _, _) = emit_skip_weights(
        sb,
        macs,
        s_nodes,
        den6,
        is_w,
        chals[p.inner_skip.ch],
        vals,
        consts,
        k,
    );
    let w_w = emit_dot(sb, macs, &skip_ab, &zp_w, k);

    // ---- the claims' points as (native, wire) pairs, located by value ----
    let mut cands: Vec<(F128, Wire)> = vec![(F128::ZERO, zw), (F128::ONE, ow)];
    cands.extend(p.zc_rounds.iter().map(|r| (chals[r.sq.ch], sq_w(r.sq))));
    cands.extend(p.lc_rounds.iter().map(|r| (chals[r.sq.ch], sq_w(r.sq))));
    cands.extend(r_outer_n.iter().copied().zip(r_outer_w.iter().copied()));
    cands.extend(p.io.iter().map(|&s| (chals[s.ch], sq_w(s))));
    for &b in &baked {
        let w = cw(sb, vals, consts, b);
        cands.push((b, w));
    }
    let locate = |xs: &[F128], what: &str| -> Vec<(F128, Wire)> {
        xs.iter()
            .enumerate()
            .map(|(i, &x)| {
                let found: Vec<Wire> = cands
                    .iter()
                    .filter(|&&(v, _)| v == x)
                    .map(|&(_, w)| w)
                    .collect();
                assert!(!found.is_empty(), "{what} coordinate {i} is a located wire");
                (x, found[0])
            })
            .collect()
    };
    let xab = locate(&t.x_ab_n, "ab");
    let xc = locate(&t.x_c_n, "c");
    let xpd = locate(&t.child.pd_point, "published-word");
    assert_eq!(
        t.child.ab.point.z_skip.phi8(),
        chals[p.inner_skip.ch],
        "the ab claim's skip point"
    );
    assert_eq!(
        t.child.c.point.z_skip.phi8(),
        z_n,
        "the c claim's skip point"
    );
    assert_eq!(
        t.child.c.value, c_eval_n,
        "the c claim's value is the interpolated one"
    );

    // ---- the ring-switch claim checks ----
    let shv = |kk: usize| -> Vec<Wire> {
        (0..RS_SHAT_WORDS)
            .map(|i| wv(t.rs_recs[kk].0 + i))
            .collect()
    };
    emit_claim_check(sb, macs, &skip_ab, xab[0].1, &shv(0), w_w, k);
    emit_claim_check(sb, macs, &skip_c, xc[0].1, &shv(1), c_eval_w, k);

    // ---- the anchor expect: the single-column layout weight derived in-circuit ----
    let m_mp2 = t.m_mp2;
    let n_log_i = t.n_log_i;
    let rho_mrg_n: Vec<F128> = t.w_rounds.iter().map(|rr| chals[rr.ch]).collect();
    let rho_mrg_w: Vec<Wire> = t
        .w_rounds
        .iter()
        .map(|rr| outs[trace.squeezes[rr.fin][0]][0])
        .collect();
    let spine = cs.spine;
    let mut rinv_n = rho_mrg_n.clone();
    let mut rinv_w = rho_mrg_w.clone();
    let mut ghat = zw;
    for j in 0..RS_SHAT_WORDS {
        if j > 0 {
            let mut lvl_w = Vec::with_capacity(m_mp2);
            for t2 in 0..m_mp2 {
                let y = flock_core::pcs::jagged::frob_inv(rinv_n[t2]);
                rinv_n[t2] = y;
                vals.push(y);
                let yw = sb.input();
                let d = sb.gate(spine, &[zw, zw, zw, rinv_w[t2], zw, zw, yw, yw, zw])[3];
                sb.connect(d, zassert);
                lvl_w.push(yw);
            }
            rinv_w = lvl_w;
        }
        let factors: Vec<(Wire, Wire)> = rinv_w
            .iter()
            .copied()
            .zip(mp_rho2_w.iter().copied())
            .collect();
        let eqj = prefix_product(sb, pfslot, pf_w, zw, ow, &factors);
        ghat = sb.gate(spine, &[zw, zw, zw, ghat, zw, zw, mp_pws[j], eqj, zw])[3];
    }
    let e_at_w = {
        let factors: Vec<(Wire, Wire)> = rho_mrg_w
            .iter()
            .copied()
            .zip(mp_rho2_w.iter().copied())
            .collect();
        prefix_product(sb, pfslot, pf_w, zw, ow, &factors)
    };
    let w_layout = {
        let mut acc = zw;
        for &(c, t_c, t_next) in &t.run_consts {
            let mut factors = Vec::with_capacity(2 * (m_mp2 + 1));
            for l in 0..=m_mp2 {
                factors.push((mp_sig_w[2 * l], if (t_c >> l) & 1 == 1 { ow } else { zw }));
                factors.push((
                    mp_sig_w[2 * l + 1],
                    if (t_next >> l) & 1 == 1 { ow } else { zw },
                ));
            }
            let e = prefix_product(sb, pfslot, pf_w, zw, ow, &factors);
            let c_w = cw(sb, vals, consts, c);
            acc = sb.gate(macs, &[acc, c_w, e])[0];
        }
        acc
    };
    let alslot = cs.alslot;
    let dp = |sb: &mut ShapeBuilder, z_row: &[Wire]| -> Wire {
        let mut gdp = [zw, zw, ow, zw];
        for layer in (0..=m_mp2).rev() {
            let za = if layer < n_log_i { z_row[layer] } else { zw };
            let rb = if layer < m_mp2 { mp_rho2_w[layer] } else { zw };
            let mut a_in = gdp.to_vec();
            a_in.extend_from_slice(&[za, rb, mp_sig_w[2 * layer], mp_sig_w[2 * layer + 1], ow]);
            let o = sb.gate(alslot, &a_in);
            gdp = [o[0], o[1], o[2], o[3]];
        }
        gdp[0]
    };
    let mut expect_w = zw;
    for (si, xs) in [&xab, &xc].iter().enumerate() {
        let z_row: Vec<Wire> = xs[1..1 + n_log_i].iter().map(|&(_, w)| w).collect();
        let d = dp(sb, &z_row);
        let coeff = if si == 0 {
            ghat
        } else {
            sb.gate(
                spine,
                &[zw, zw, zw, zw, zw, zw, mp_pws[RS_SHAT_WORDS], ghat, zw],
            )[3]
        };
        let wd = sb.gate(spine, &[zw, zw, zw, zw, zw, zw, w_layout, d, zw])[3];
        expect_w = sb.gate(spine, &[zw, zw, zw, expect_w, zw, zw, coeff, wd, zw])[3];
    }
    {
        let pd = &t.gammas_o[0];
        let gpd_w = squeeze_word_wire(&outs, trace, pd.fin, pd.squeeze_offset);
        let w_st = sb.gate(macs, &[zw, gpd_w, w_layout])[0];
        let z_row: Vec<Wire> = xpd.iter().map(|&(_, w)| w).collect();
        let d = dp(sb, &z_row);
        let coeff = sb.gate(macs, &[zw, mp_pws[2 * RS_SHAT_WORDS], e_at_w])[0];
        let wd = sb.gate(macs, &[zw, w_st, d])[0];
        expect_w = sb.gate(macs, &[expect_w, coeff, wd])[0];
    }
    sb.connect(anc_w, expect_w);

    // ---- the published words: hashed to the absorbed digest, and their claim evaluated ----
    let words: Vec<F128> = t.child.rows.iter().flatten().copied().collect();
    let digest_w = payload_wires(p.digest_payload);
    let word_w = crate::tower::emit_publics_hash(
        sb,
        cs.q,
        iv2,
        &words,
        [digest_w[0], digest_w[1]],
        vals,
        consts,
    );
    {
        let width = t.child.rows[0].len();
        let words_log = width.trailing_zeros() as usize;
        let io_w: Vec<Wire> = p.io.iter().map(|&s| sq_w(s)).collect();
        assert_eq!(
            1usize << (io_w.len() - words_log),
            t.child.rows.len(),
            "one row coordinate per row bit"
        );
        let e_word = emit_eq_tensor(sb, macs, &io_w[..words_log], k);
        let e_row = emit_eq_tensor(sb, macs, &io_w[words_log..], k);
        let mut value = zw;
        for (j, row) in word_w.chunks(width).enumerate() {
            let inner = emit_dot(sb, macs, &e_word, row, k);
            value = sb.gate(macs, &[value, e_row[j], inner])[0];
        }
        sb.connect(value, wv(t.gammas_o[0].val_v));
    }

    // ---- the lincheck equation α·a + b + β·C(konst) = running, a and b claims to fold ----
    let values: [Wire; 2] = t.child.lc_claims.each_ref().map(|c| {
        vals.push(c.value);
        sb.input()
    });
    let rr_w: Vec<Wire> = p.lc_rounds.iter().rev().map(|r| sq_w(r.sq)).collect();
    let konst = t.child.konst;
    let bits: Vec<(Wire, Wire)> = rr_w
        .iter()
        .enumerate()
        .map(|(j, &r)| {
            (
                r,
                if (konst >> (K_SKIP + j)) & 1 == 1 {
                    ow
                } else {
                    zw
                },
            )
        })
        .collect();
    let eq_konst = prefix_product(sb, pfslot, pf_w, zw, ow, &bits);
    let c_konst = sb.gate(macs, &[zw, zp_w[konst & (Z_PARTIAL_WORDS - 1)], eq_konst])[0];
    let lhs = sb.gate(macs, &[values[1], alpha_w, values[0]])[0];
    let lhs = sb.gate(macs, &[lhs, beta_w, c_konst])[0];
    let delta = sb.gate(macs, &[lhs, lc_w, ow])[0];
    sb.connect(delta, zassert);
    let row = &t.child.lc_claims[0].row;
    let col = &t.child.lc_claims[0].col;
    for c in &t.child.lc_claims {
        assert_eq!(
            (&c.row, &c.col),
            (row, col),
            "the two claims share their weights"
        );
    }
    assert_eq!(
        row.low,
        SkipPoint::Phi8(z_n).weights(K_SKIP),
        "the row low is the skip functional"
    );
    assert_eq!(
        col.low,
        t.vals_rec[p.zp_v..p.zp_v + Z_PARTIAL_WORDS],
        "the column low is z_partial"
    );
    assert_eq!(
        col.point,
        p.lc_rounds
            .iter()
            .rev()
            .map(|r| chals[r.sq.ch])
            .collect::<Vec<_>>(),
        "the column point is the lincheck rounds, reversed"
    );
    let row_pt: Vec<Wire> = locate(&row.point, "lincheck row")
        .into_iter()
        .map(|(_, w)| w)
        .collect();
    let surface = FoldSurface {
        row_low: skip_c.clone(),
        row_pt,
        col_low: zp_w.clone(),
        col_pt: rr_w,
        values,
    };

    // ---- the tail: what the wrap's verifier checks natively ----
    let tail = vec![
        Tail {
            name: "statement digest",
            wires: payload_wires(p.digest_payload),
        },
        Tail {
            name: "r1cs digest",
            wires: payload_wires(p.r1cs_payload),
        },
        Tail {
            name: "level sums",
            wires: level_accs.iter().flatten().copied().collect(),
        },
        Tail {
            name: "anchor end",
            wires: vec![anc_w],
        },
        Tail {
            name: "spine final",
            wires: t_final.to_vec(),
        },
    ];
    (tail, surface)
}

/// The native values a region's tail must carry, in tail order.
pub(super) fn expected_rowmajor_tail(t: &RowMajorTape<'_>) -> Vec<(&'static str, Vec<F128>)> {
    let p = &t.piop;
    let payload = |pi: usize| -> Vec<F128> {
        crate::tower::payload_words(&t.stream)[pi]
            .iter()
            .map(|&wi| {
                let b = &t.bytes[wi * 16..wi * 16 + 16];
                F128::new(
                    u64::from_le_bytes(b[..8].try_into().unwrap()),
                    u64::from_le_bytes(b[8..].try_into().unwrap()),
                )
            })
            .collect()
    };
    vec![
        ("statement digest", payload(p.digest_payload)),
        ("r1cs digest", payload(p.r1cs_payload)),
        (
            "level sums",
            t.native_sums.iter().flat_map(|s| [s.c0, s.c1]).collect(),
        ),
        ("anchor end", vec![t.anc_end_n]),
        ("spine final", vec![t.t_final_n.c0, t.t_final_n.c1]),
    ]
}

/// The published tail of one child in the wrap's public segment: per block, its name, offset and
/// width.
pub type TailLayout = Vec<(&'static str, usize, usize)>;

const FOLD_DOMAIN: &[u8] = b"flock-rowmajor-wrap-fold-v0";

/// A recorded run of matrix folds, then jagged folds, on one transcript: its tape, its located
/// groups and its accumulated claims.
pub(super) struct FoldTape {
    pub(super) ops: Vec<Op>,
    pub(super) vals_rec: Vec<F128>,
    pub(super) chals: Vec<F128>,
    pub(super) trace: FsChainTrace,
    pub(super) stream: Stream,
    pub(super) bytes: Vec<u8>,
    pub(super) cross: Vec<Option<(usize, usize)>>,
    pub(super) locs: Vec<super::fold_region::FoldLoc>,
    pub(super) jlocs: Vec<super::fold_region::JaggedFoldLoc>,
    pub(super) clocs: Vec<(usize, usize)>,
    pub(super) outs: Vec<MatrixClaim>,
    pub(super) jouts: Vec<MatrixClaim>,
    /// The payload ordinal of each jagged group's key.
    pub(super) jag_payloads: Vec<usize>,
    /// For the wrap's lincheck fold: per matrix group, the matrix it folds and where each of its
    /// claims comes from, and each matrix's last group.
    lc_plan: Vec<(usize, Vec<LcSrc>)>,
    lc_top: [usize; 2],
}

/// Where a claim of the wrap's lincheck fold comes from: a chunk, or an earlier group's output.
#[derive(Clone, Copy, Debug)]
enum LcSrc {
    Chunk(usize),
    Group(usize),
}

/// Chunks whose lincheck claims one fold group takes: each claim holds two vectors of the block's
/// size while its group folds.
const LC_BATCH: usize = 4;

impl FoldTape {
    /// Locates the folds `rec` recorded: the matrix groups `claims` with their proofs, then the
    /// jagged groups `jagged` with theirs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn located(
        rec: RecordingChallenger<FsChallenger>,
        domain: &[u8],
        claims: &[Vec<MatrixClaim>],
        proofs: &[FoldProof],
        outs: Vec<MatrixClaim>,
        jagged: &[([u8; 32], Vec<flock_core::matrix_fold::JaggedClaim>)],
        jproofs: &[FoldProof],
        jouts: Vec<MatrixClaim>,
    ) -> FoldTape {
        use super::fold_region::{
            challenge_word_locs, labeled_bytes_payloads, locate_and_pin_folds,
            locate_and_pin_jagged_folds, replay_fold_endpoints, replay_jagged_fold_endpoints,
        };
        let t_shape = rec.shape();
        let ops: Vec<Op> = flatten_ops(t_shape.ops()).to_vec();
        let vals_rec = rec.values().to_vec();
        let chals = rec.challenges().to_vec();
        let proof_refs: Vec<&FoldProof> = proofs.iter().collect();
        let (locs, vcur, ccur) = locate_and_pin_folds(claims, &proof_refs, &vals_rec, &chals);
        assert_eq!(
            replay_fold_endpoints(&locs, &vals_rec, &chals),
            outs,
            "the matrix folds' outputs replay from their tape"
        );
        let jag_payloads = labeled_bytes_payloads(&ops, b"flock-aggregate-jagged-v0");
        let jrefs: Vec<&FoldProof> = jproofs.iter().collect();
        let jlocs = locate_and_pin_jagged_folds(
            jagged,
            &jrefs,
            &vals_rec,
            &chals,
            rec.payloads(),
            &jag_payloads,
            vcur,
            ccur,
        );
        assert_eq!(
            replay_jagged_fold_endpoints(&jlocs, &vals_rec, &chals),
            jouts,
            "the jagged folds' outputs replay from their tape"
        );
        let mc = walker_common::merge_and_replay_chain(
            &t_shape,
            domain,
            rec.values(),
            rec.payloads(),
            &ops,
            &chals,
        );
        FoldTape {
            clocs: challenge_word_locs(t_shape.ops()),
            ops,
            vals_rec,
            chals,
            trace: mc.trace,
            stream: mc.stream,
            bytes: mc.bytes,
            cross: mc.cross,
            locs,
            jlocs,
            outs,
            jouts,
            jag_payloads,
            lc_plan: Vec::new(),
            lc_top: [0, 0],
        }
    }

    /// Records the fold of the chunks' lincheck claims, per matrix: batches of at most
    /// [`LC_BATCH`] chunks, then the batches' outputs, so that no group holds more than a batch's
    /// vectors.
    fn new(children: &[RowMajorChild<'_>], mats: [&dyn FoldMatrix; 2]) -> FoldTape {
        use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
        let mut rec = RecordingChallenger::new(FsChallenger::with_chained_blake3(FOLD_DOMAIN));
        let grinding = FoldGrinding::per_challenge_128();
        let mut claims: Vec<Vec<MatrixClaim>> = Vec::new();
        let mut proofs = Vec::new();
        let mut outs: Vec<MatrixClaim> = Vec::new();
        let mut plan: Vec<(usize, Vec<LcSrc>)> = Vec::new();
        let mut top = [0usize; 2];
        let trace = std::env::var_os("WRAP_TIMING").is_some();
        for (m, mat) in mats.iter().enumerate() {
            let mut level: Vec<(LcSrc, MatrixClaim)> = children
                .iter()
                .enumerate()
                .map(|(j, c)| (LcSrc::Chunk(j), c.lc_claims[m].clone()))
                .collect();
            loop {
                let mut next = Vec::new();
                for batch in level.chunks(LC_BATCH) {
                    let cs: Vec<MatrixClaim> = batch.iter().map(|(_, c)| c.clone()).collect();
                    let combs: Vec<Vec<F128>> = cs
                        .par_iter()
                        .map(|c| mat.col_marginal(&c.row.materialize(), mat.n_cols()))
                        .collect();
                    let tq = std::time::Instant::now();
                    let (fp, out) =
                        prove_fold_with_grinding_owned(*mat, combs, &cs, grinding, &mut rec);
                    if trace {
                        eprintln!(
                            "[wrap] fold {m}: k_row {} k_col {} claims {} {:.2} s",
                            cs[0].row.n_vars(),
                            cs[0].col.n_vars(),
                            cs.len(),
                            tq.elapsed().as_secs_f64()
                        );
                    }
                    next.push((LcSrc::Group(claims.len()), out.clone()));
                    plan.push((m, batch.iter().map(|&(src, _)| src).collect()));
                    claims.push(cs);
                    proofs.push(fp);
                    outs.push(out);
                }
                level = next;
                if level.len() == 1 {
                    break;
                }
            }
            top[m] = claims.len() - 1;
        }
        let mut ft = FoldTape::located(
            rec,
            FOLD_DOMAIN,
            &claims,
            &proofs,
            outs,
            &[],
            &[],
            Vec::new(),
        );
        ft.lc_plan = plan;
        ft.lc_top = top;
        ft
    }
}

/// The emitted folds of a [`FoldTape`]: per matrix group its accumulated claim's
/// `(ρ_col, ρ_row, value)` wires, per jagged group its published entry, and the transcript's
/// stream wires, through which a caller ties each claim's surface.
pub(super) struct FoldEmit {
    pub(super) groups: Vec<(Vec<Wire>, Vec<Wire>, Wire)>,
    pub(super) jagged: Vec<super::fold_region::FoldPub>,
    ww: Vec<Option<Wire>>,
    vmap: Vec<Option<usize>>,
}

impl FoldEmit {
    /// The wire of the tape's `vi`-th observed value.
    pub(super) fn wv(&self, vi: usize) -> Wire {
        self.ww[self.vmap[vi].expect("stream word")].expect("wired")
    }

    /// The wires of the tape's `p`-th byte payload.
    pub(super) fn payload(&self, ft: &FoldTape, p: usize) -> Vec<Wire> {
        crate::tower::payload_words(&ft.stream)[p]
            .iter()
            .map(|&wi| self.ww[wi].expect("payload word wired"))
            .collect()
    }
}

/// Emits a recorded run of folds: its transcript, its two sumchecks per group and every claim
/// weight at the fold's points, all in-circuit (the low factors' boundary products derived from
/// the challenge wires); the claims' surfaces are left for the caller to tie.
pub(super) fn emit_folds(
    sb: &mut ShapeBuilder,
    cs: &mut ChildSlots,
    k: Consts,
    ft: &FoldTape,
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> FoldEmit {
    use crate::tower::{LeafEvalGate, envelope::slot_cached, gates_spine::PrefixGate};
    let (zw, ow) = (k.zw, k.ow);
    let macs = cs.macs;
    let iv_w = pack8(&IV);
    let iv2 = [cw(sb, vals, consts, iv_w[0]), cw(sb, vals, consts, iv_w[1])];
    let n_payloads = ft.ops.iter().filter(|o| o.carries_payload()).count();
    let (outs, ww) = emit_fiat_shamir_chain(
        sb,
        cs.q.b3,
        iv2,
        &ft.trace,
        &ft.stream,
        &ft.bytes,
        vals,
        consts,
        &vec![false; n_payloads],
        &ft.cross,
    );
    emit_recorded_pow_checks(
        sb, cs.q.b3, cs.q.pow, iv2, &ft.ops, &ft.trace, &ft.stream, &outs, &ww, vals, consts,
    );
    let mut vmap: Vec<Option<usize>> = Vec::new();
    for (wi, w) in ft.stream.words.iter().enumerate() {
        if let StreamWord::Value(vi) = *w {
            if vmap.len() <= vi {
                vmap.resize(vi + 1, None);
            }
            vmap[vi] = Some(wi);
        }
    }
    let wv = |vi: usize| -> Wire { ww[vmap[vi].expect("stream word")].expect("wired") };
    let chw = |ch: usize| -> Wire {
        let (fin, offset) = ft.clocs[ch];
        squeeze_word_wire(&outs, &ft.trace, fin, offset)
    };
    let pf_w = 8usize;
    let pfslot = slot_cached(sb, &mut cs.resid, 310 + pf_w, || PrefixGate::new(pf_w));
    let leslot = match cs.le.iter().find(|&&(n, _)| n == 8) {
        Some(&(_, sl)) => sl,
        None => {
            let sl = sb.slot(LeafEvalGate::new(8));
            cs.le.push((8, sl));
            sl
        }
    };
    let weight = |sb: &mut ShapeBuilder,
                  low_v: usize,
                  low_n: usize,
                  pt_v: usize,
                  pt_n: usize,
                  rho: &[Wire]|
     -> Wire {
        let s2 = low_n.trailing_zeros() as usize;
        let seed = if low_n == 1 {
            wv(low_v)
        } else {
            assert_eq!(low_n, 64, "the lincheck low width");
            let mut acc = zw;
            for h in 0..8 {
                let mut a = ow;
                for b in 0..3 {
                    let r = rho[3 + b];
                    let f = if (h >> b) & 1 == 1 {
                        r
                    } else {
                        sb.gate(macs, &[r, ow, ow])[0]
                    };
                    a = sb.gate(macs, &[zw, a, f])[0];
                }
                let mut g_in: Vec<Wire> = (0..8).map(|j| wv(low_v + 8 * h + j)).collect();
                g_in.extend([rho[0], rho[1], rho[2]]);
                g_in.push(a);
                g_in.push(acc);
                acc = sb.gate(leslot, &g_in)[0];
            }
            acc
        };
        let fs: Vec<(Wire, Wire)> = (0..pt_n).map(|j| (wv(pt_v + j), rho[s2 + j])).collect();
        prefix_product_seeded(sb, pfslot, pf_w, zw, ow, seed, &fs)
    };
    let mut groups = Vec::new();
    for (fi, loc) in ft.locs.iter().enumerate() {
        let kk = loc.claims.len();
        let lam_w: Vec<Wire> = (0..kk).map(|i| chw(loc.lam_ch0 + i)).collect();
        let mut run_w = zw;
        for (i, cl) in loc.claims.iter().enumerate() {
            run_w = sb.gate(macs, &[run_w, lam_w[i], wv(cl.value_v)])[0];
        }
        let mut rho_col: Vec<Wire> = Vec::with_capacity(loc.k_col);
        for j in 0..loc.k_col {
            let r_w = chw(loc.col_ch0 + j);
            rho_col.push(r_w);
            run_w = sb.gate(
                cs.mrs,
                &[run_w, wv(loc.col_v + 2 * j), wv(loc.col_v + 2 * j + 1), r_w],
            )[0];
        }
        let mut exp_w = zw;
        for (i, cl) in loc.claims.iter().enumerate() {
            let w = weight(
                sb,
                cl.col_low_v,
                cl.col_low_n,
                cl.col_pt_v,
                cl.col_pt_n,
                &rho_col,
            );
            let t2 = sb.gate(macs, &[zw, w, wv(loc.bridge_v + i)])[0];
            exp_w = sb.gate(macs, &[exp_w, lam_w[i], t2])[0];
        }
        sb.connect(run_w, exp_w);
        let mu_w: Vec<Wire> = (0..kk).map(|i| chw(loc.mu_ch0 + i)).collect();
        let mut run2 = zw;
        for i in 0..kk {
            run2 = sb.gate(macs, &[run2, mu_w[i], wv(loc.bridge_v + i)])[0];
        }
        let mut rho_row: Vec<Wire> = Vec::with_capacity(loc.k_row);
        for j in 0..loc.k_row {
            let r_w = chw(loc.row_ch0 + j);
            rho_row.push(r_w);
            run2 = sb.gate(
                cs.mrs,
                &[run2, wv(loc.row_v + 2 * j), wv(loc.row_v + 2 * j + 1), r_w],
            )[0];
        }
        let mut wmu = zw;
        for (i, cl) in loc.claims.iter().enumerate() {
            let w = weight(
                sb,
                cl.row_low_v,
                cl.row_low_n,
                cl.row_pt_v,
                cl.row_pt_n,
                &rho_row,
            );
            wmu = sb.gate(macs, &[wmu, mu_w[i], w])[0];
        }
        let value = if fi + 1 == ft.locs.len() && ft.jlocs.is_empty() {
            vals.push(ft.vals_rec[loc.out_v]);
            sb.input()
        } else {
            wv(loc.out_v)
        };
        let rhs = sb.gate(macs, &[zw, wmu, value])[0];
        sb.connect(run2, rhs);
        groups.push((rho_col, rho_row, value));
    }
    let jagged = super::fold_region::emit_jagged_fold_region(
        sb,
        macs,
        cs.mrs,
        pfslot,
        pf_w,
        &ft.jlocs,
        &ft.trace,
        &ft.clocs,
        &outs,
        &ww,
        &vmap,
        &ft.vals_rec,
        vals,
        zw,
        ow,
    );
    FoldEmit {
        groups,
        jagged,
        ww,
        vmap,
    }
}

/// Emits the fold of the chunks' lincheck claims, each claim's surface tied to its chunk region's
/// wires; returns, per group, the accumulated claim's `(ρ_col, ρ_row, value)` wires.
fn emit_lincheck_fold(
    sb: &mut ShapeBuilder,
    cs: &mut ChildSlots,
    k: Consts,
    ft: &FoldTape,
    surfaces: &[FoldSurface],
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> Vec<(Vec<Wire>, Vec<Wire>, Wire)> {
    let fe = emit_folds(sb, cs, k, ft, vals, consts);
    let tie = |sb: &mut ShapeBuilder, at: usize, n: usize, ws: &[Wire]| {
        assert_eq!(n, ws.len(), "a claim surface's width");
        for (j, &w) in ws.iter().enumerate() {
            sb.connect(fe.wv(at + j), w);
        }
    };
    for (loc, (m, srcs)) in ft.locs.iter().zip(&ft.lc_plan) {
        for (cl, src) in loc.claims.iter().zip(srcs) {
            match *src {
                LcSrc::Chunk(j) => {
                    let sf = &surfaces[j];
                    tie(sb, cl.row_low_v, cl.row_low_n, &sf.row_low);
                    tie(sb, cl.row_pt_v, cl.row_pt_n, &sf.row_pt);
                    tie(sb, cl.col_low_v, cl.col_low_n, &sf.col_low);
                    tie(sb, cl.col_pt_v, cl.col_pt_n, &sf.col_pt);
                    sb.connect(fe.wv(cl.value_v), sf.values[*m]);
                }
                LcSrc::Group(g) => {
                    let (rho_col, rho_row, value) = &fe.groups[g];
                    tie(sb, cl.row_low_v, cl.row_low_n, &[k.ow]);
                    tie(sb, cl.row_pt_v, cl.row_pt_n, rho_row);
                    tie(sb, cl.col_low_v, cl.col_low_n, &[k.ow]);
                    tie(sb, cl.col_pt_v, cl.col_pt_n, rho_col);
                    sb.connect(fe.wv(cl.value_v), *value);
                }
            }
        }
    }
    ft.lc_top.iter().map(|&g| fe.groups[g].clone()).collect()
}

/// `seed · Π (1 + a_j + b_j)` through the prefix slot.
pub(super) fn prefix_product_seeded(
    sb: &mut ShapeBuilder,
    pfslot: SlotId,
    pf_w: usize,
    zw: Wire,
    ow: Wire,
    seed: Wire,
    fs: &[(Wire, Wire)],
) -> Wire {
    let mut s = seed;
    for chunk in fs.chunks(pf_w) {
        let mut g_in = vec![s];
        g_in.extend(chunk.iter().map(|&(a, _)| a));
        g_in.extend(std::iter::repeat_n(zw, pf_w - chunk.len()));
        g_in.extend(chunk.iter().map(|&(_, b)| b));
        g_in.extend(std::iter::repeat_n(zw, pf_w - chunk.len()));
        g_in.push(ow);
        s = sb.gate(pfslot, &g_in)[0];
    }
    s
}

/// Emits the parent compression `P(l, r)` of two digests.
pub(super) fn emit_parent(
    sb: &mut ShapeBuilder,
    b3: SlotId,
    l: [Wire; 2],
    r: [Wire; 2],
    vals: &mut Vec<F128>,
    consts: &mut Vec<(F128, Wire)>,
) -> [Wire; 2] {
    use crate::tower::{PARENT, pack_params};
    let iv_w = pack8(&IV);
    let iv2 = [cw(sb, vals, consts, iv_w[0]), cw(sb, vals, consts, iv_w[1])];
    let params = cw(sb, vals, consts, pack_params(0, 64, PARENT));
    let out = sb.gate(b3, &[iv2[0], iv2[1], l[0], l[1], r[0], r[1], params]);
    [out[0], out[1]]
}

/// The parent compression `P(l, r)` of two digests, natively.
pub fn parent_digest(l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    use flock_merkle::{Blake3MerkleHash, MerkleHash};
    Blake3MerkleHash::hash_pair(l, r)
}

/// What one emission of the wrap circuit hands back.
struct WrapBuild {
    eb: EnvBuild,
    tails: Vec<TailLayout>,
    acc: Vec<(usize, usize, usize)>,
    need: usize,
    census: EnvCensus,
    block_base: usize,
}

fn emit_wrap(
    tapes: &[RowMajorTape<'_>],
    fold: &FoldTape,
    env: &HeadEnv,
    nu: usize,
    spread_decl: usize,
    spread_w: usize,
) -> WrapBuild {
    let mut eb = EnvBuild::begin(env, nu, spread_decl);
    let k = eb.k;
    let (tails, acc_w, block) = {
        let EnvBuild {
            sb,
            cs,
            vals,
            hints,
            consts,
            ..
        } = &mut eb;
        let (tails, surfaces): (Vec<Vec<Tail>>, Vec<FoldSurface>) = tapes
            .iter()
            .map(|t| {
                let isl = sb.begin_island();
                let out = emit_rowmajor_region(sb, cs, t, k, vals, hints, consts);
                sb.end_island(isl);
                out
            })
            .unzip();
        let acc_w = emit_lincheck_fold(sb, cs, k, fold, &surfaces, vals, consts);
        let digest = |tail: &[Tail]| -> [Wire; 2] {
            let w = &tail
                .iter()
                .find(|b| b.name == "statement digest")
                .expect("a statement digest")
                .wires;
            [w[0], w[1]]
        };
        let mut d = digest(&tails[0]);
        for tail in &tails[1..] {
            d = emit_parent(sb, cs.q.b3, d, digest(tail), vals, consts);
        }
        let layouts: Vec<TailLayout> = tails
            .iter()
            .map(|tail| {
                tail.iter()
                    .map(|b| {
                        let at = sb.public_len();
                        for &w in &b.wires {
                            sb.publish(w);
                        }
                        (b.name, at, b.wires.len())
                    })
                    .collect()
            })
            .collect();
        let mut block = vec![d[0], d[1]];
        for (rho_col, rho_row, value) in &acc_w {
            block.extend_from_slice(rho_col);
            block.extend_from_slice(rho_row);
            block.push(*value);
        }
        let acc_w: Vec<(usize, usize)> = acc_w.iter().map(|(c, r, _)| (c.len(), r.len())).collect();
        (layouts, acc_w, block)
    };
    let need = slot_list(&eb.cs)
        .iter()
        .map(|&(_, s)| eb.sb.rows_in_slot(s))
        .max()
        .unwrap_or(0);
    let census = eb.finish(env, &block, spread_w, &[]);
    let block_base = if env.measure { census.body } else { env.body };
    let mut at = block_base + 2;
    let acc = acc_w
        .iter()
        .map(|&(kc, kr)| {
            let o = at;
            at += kc + kr + 1;
            (o, kc, kr)
        })
        .collect();
    WrapBuild {
        eb,
        tails,
        acc,
        need,
        census,
        block_base,
    }
}

/// What a wrap's verifier holds: the circuit's key, where each chunk's tail and each accumulated
/// lincheck claim sit in the public segment, and what the circuit used of its envelope.
pub struct WrapKey {
    /// The circuit's key.
    pub key: EnvKey,
    /// Per child, where its tail sits in the public segment.
    pub tails: Vec<TailLayout>,
    /// Where each accumulated lincheck claim (on `A`, then `B`) sits in the public segment:
    /// `(offset, column variables, row variables)`, laid out `[ρ_col | ρ_row | value]`.
    pub acc: Vec<(usize, usize, usize)>,
    /// Where the head block, which opens with the block digest, starts in the public segment.
    pub block: usize,
    /// What the circuit used of its envelope.
    pub census: EnvCensus,
}

/// A wrap proof.
pub type WrapProof = EnvProof;

/// Phase timings of a wrap, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct WrapTimings {
    /// Parsing the children's transcripts.
    pub tapes: f64,
    /// Building the circuit shape.
    pub build: f64,
    /// Running the witness.
    pub witness: f64,
    /// Proving the outer circuit.
    pub prove: f64,
}

/// Wraps `children` in one union-circuit proof built to `env`, whose dense stack `outer` commits
/// and opens, or Ligerito when it is `None`.
pub fn prove_wrap(
    children: &[RowMajorChild<'_>],
    mats: [&dyn FoldMatrix; 2],
    env: &HeadEnv,
    outer: Option<&dyn OuterPcs>,
) -> (WrapKey, WrapProof, WrapTimings) {
    use std::time::Instant;
    let mut timings = WrapTimings::default();
    let t0 = Instant::now();
    let tapes: Vec<RowMajorTape<'_>> = children.iter().map(RowMajorTape::new).collect();
    timings.tapes = t0.elapsed().as_secs_f64();
    let t0 = Instant::now();
    let spread_w = tapes
        .iter()
        .map(|t| t.spread_w)
        .max()
        .expect("at least one child");
    let trace_t = std::env::var_os("WRAP_TIMING").is_some();
    let tf = Instant::now();
    let fold = FoldTape::new(children, mats);
    if trace_t {
        eprintln!("[wrap] fold prove {:.2} s", tf.elapsed().as_secs_f64());
    }
    let (nu, sw) = if env.measure && env.nu > 0 {
        (env.nu, spread_w)
    } else if env.measure {
        let wb = emit_wrap(&tapes, &fold, env, 24, spread_w, spread_w);
        let nu = (wb.need.next_power_of_two().trailing_zeros() as usize).max(7);
        (nu, spread_w)
    } else {
        (env.nu, env.spread_w.max(spread_w))
    };
    let WrapBuild {
        eb,
        tails,
        acc,
        census,
        block_base,
        ..
    } = emit_wrap(&tapes, &fold, env, nu, sw, spread_w);
    let t_emit = t0.elapsed().as_secs_f64();
    let (key, proof, tm) = prove_env(eb, nu, sw, outer, |public| {
        for (t, layout) in tapes.iter().zip(&tails) {
            for ((name, at, len), (_, want)) in layout.iter().zip(expected_rowmajor_tail(t)) {
                assert_eq!(&public[*at..at + len], &want[..], "the published {name}");
            }
        }
    });
    timings.build = t_emit + tm.build;
    timings.witness = tm.witness;
    timings.prove = tm.prove;
    (
        WrapKey {
            key,
            tails,
            acc,
            block: block_base,
            census,
        },
        proof,
        timings,
    )
}

/// Verifies a wrap proof's outer circuit proof under `key`; the caller then checks its block digest
/// against the statements and discharges its accumulated lincheck claims.
pub fn verify_wrap(
    key: &WrapKey,
    proof: &WrapProof,
    outer: Option<&dyn OuterPcs>,
) -> Result<(), flock_core::verifier::FlockVerifyError> {
    key.key.verify(proof, outer)
}

/// Builds and runs a standalone circuit verifying one wrap proof, opened through `outer` and
/// described by `whir_rec`, holding every published value against the native replay; returns the
/// circuit's BLAKE3 rows and every slot's largest row count.
pub fn build_head_circuit(
    key: &WrapKey,
    proof: &WrapProof,
    outer: &dyn OuterPcs,
    whir_rec: &super::whir_circuit::WhirRecord,
) -> (usize, usize) {
    use crate::tower::head_walker::{HeadTape, check_head_region, emit_head_region};
    let lo = key.key.leaf_outer(proof);
    let tape = HeadTape::new(&lo, ENV_DOMAIN, outer, whir_rec);
    let mut nu = 24usize;
    let mut measured = false;
    loop {
        let mut sb = ShapeBuilder::new(nu);
        let spread = tape.spread_w.max(lo.shape.circuit.cells().mu());
        let mut cs = ChildSlots::new(&mut sb, nu, spread);
        let mut vals: Vec<F128> = Vec::new();
        let mut hints: Vec<[u32; SLOT_WORDS]> = Vec::new();
        let mut consts: Vec<(F128, Wire)> = Vec::new();
        let k = Consts::new(&mut sb, &mut vals);
        let b3 = cs.q.b3;
        let region = emit_head_region(
            &mut sb,
            &mut cs,
            b3,
            &tape,
            k,
            &mut vals,
            &mut hints,
            &mut consts,
        );
        let mut need = [
            cs.q.b3,
            cs.q.swap,
            cs.q.spread,
            cs.q.pow,
            cs.macs,
            cs.fold_macs,
            cs.zcr,
            cs.mrs,
            cs.spine,
            cs.spine256,
            cs.alslot,
        ]
        .iter()
        .map(|&x| sb.rows_in_slot(x))
        .max()
        .unwrap();
        for &(_, x) in cs.le.iter().chain(cs.resid.iter()) {
            need = need.max(sb.rows_in_slot(x));
        }
        if let Some(f) = cs.q.family {
            need = need.max(sb.rows_in_slot(f));
        }
        if !measured {
            nu = (need.next_power_of_two().trailing_zeros() as usize).max(7);
            measured = true;
            continue;
        }
        let b3_rows = sb.rows_in_slot(b3);
        let shape = sb.finish().expect("the head circuit builds");
        let hint_refs: Vec<&(dyn Any + Sync)> =
            hints.iter().map(|h| h as &(dyn Any + Sync)).collect();
        let w = shape.run(&vals, &hint_refs);
        check_head_region(&w.public, &tape, &region);
        return (b3_rows, need);
    }
}
