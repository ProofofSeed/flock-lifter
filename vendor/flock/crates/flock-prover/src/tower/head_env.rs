// Added to the vendored copy of Flock; see VENDORED.md at the vendored root.
//! The envelope wraps and heads share: one slot list, one row count per slot, one public-segment
//! layout and one table of fixed public inputs, so that a head's circuit verifies either kind of
//! proof with one region.

use std::{any::Any, sync::Arc, time::Instant};

use flock_core::{
    circuit::builder::{CircuitShape, SlotId},
    lincheck::LincheckCircuit,
    pcs::{
        Commitment, OuterPcs, PcsParams,
        ligerito::{LigeritoProfile, embedded_initial_k_or_default},
    },
    proof::R1csProofCircuitMerged,
    r1cs::{BlockR1cs, SparseBinaryMatrix},
    verifier::{FlockVerifyError, verify_union_circuit_with_outer},
};

use crate::{
    prover::{UnionSlotProverInput, prove_union_circuit_with_outer},
    r1cs_hashes::blake3::generate_witness_batch_major_partial_into,
    tower::head_step::HeadLayout,
    tower::{
        BitSpreadGate, BitSpreadTable, Blake3Gate, F128, FamilyTransposeTileGate,
        FamilyTransposeTileTable, FsChallenger, HashKind, LeafEvalGate, LeafEvalGate256, LeafOuter,
        MacGate, MixedProof, PowMaskGate, PowMaskTable, PrefixGate, PrefixGate256,
        ResidualAccGate256, ResidualPrefix3Gate256, ResidualWeightsGate256, SLOT_WORDS,
        ShapeBuilder, SwapGate, SwapTable, UnionInstance, Wire, child_walker::ChildSlots, cw,
        fl_node::chain_blake_r1cs, live_element_input_from_rows, rowmajor::Consts,
    },
};

/// The shape every wrap and head circuit is built to.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct HeadEnv {
    /// Log row capacity of every slot.
    pub nu: usize,
    /// The bit-spread table's width.
    pub spread_w: usize,
    /// Keys of the slots declared after the base slots, in declaration order.
    pub keys: Vec<usize>,
    /// Padded row count per slot key.
    pub counts: Vec<(usize, usize)>,
    /// Fixed public inputs after the three shared constants, in order.
    pub table: Vec<F128>,
    /// Public words before the head block.
    pub body: usize,
    /// Words of the head block.
    pub block: usize,
    /// Whether circuits built to this envelope only measure themselves.
    pub measure: bool,
    /// The head block's layout, as the last head measured it.
    pub layout: Option<HeadLayout>,
}

/// What one circuit built to an envelope used.
#[derive(Clone, Debug, Default)]
pub struct EnvCensus {
    /// The bit-spread width the circuit needs.
    pub spread_w: usize,
    /// Rows per slot key, before padding.
    pub counts: Vec<(usize, usize)>,
    /// Every fixed public value the circuit used.
    pub table: Vec<F128>,
    /// Public words before the head block.
    pub body: usize,
    /// Words of the head block.
    pub block: usize,
    /// The head block's layout, for a head.
    pub layout: Option<HeadLayout>,
}

const BASE_KEYS: [usize; 14] = [
    9001, 9002, 9003, 9004, 9005, 9006, 9600, 9602, 9701, 9500, 9400, 9010, 9700, 9601,
];

/// Every slot of `cs` with its key: base slots under fixed keys, then the demand-created ones.
pub(super) fn slot_list(cs: &ChildSlots) -> Vec<(usize, SlotId)> {
    let mac256 = cs
        .resid
        .iter()
        .find(|&&(k, _)| k == 701)
        .expect("the F256 MAC slot")
        .1;
    let mut v = vec![
        (BASE_KEYS[0], cs.q.b3),
        (BASE_KEYS[2], cs.q.swap),
        (BASE_KEYS[3], cs.q.spread),
        (BASE_KEYS[4], cs.q.pow),
        (BASE_KEYS[6], cs.macs),
        (BASE_KEYS[7], cs.fold_macs),
        (BASE_KEYS[8], mac256),
        (BASE_KEYS[9], cs.zcr),
        (BASE_KEYS[10], cs.mrs),
        (BASE_KEYS[11], cs.spine),
        (BASE_KEYS[12], cs.spine256),
        (BASE_KEYS[13], cs.alslot),
    ];
    if let Some(s) = cs.q.b3_alt {
        v.push((BASE_KEYS[1], s));
    }
    if let Some(s) = cs.q.family {
        v.push((BASE_KEYS[5], s));
    }
    v.extend(cs.le.iter().copied());
    v.extend(
        cs.resid
            .iter()
            .filter(|&&(k, _)| k != 600 && k != 701)
            .copied(),
    );
    v.sort_by_key(|&(k, _)| k);
    v
}

/// Declares the demand-created slot of `key` in `cs`.
fn declare(sb: &mut ShapeBuilder, cs: &mut ChildSlots, key: usize) {
    match key {
        8 => {
            let s = sb.slot(LeafEvalGate::new(8));
            cs.le.push((8, s));
        }
        801..=808 => {
            let s = sb.slot(LeafEvalGate256::new(key - 800));
            cs.le.push((key, s));
        }
        603 => {
            let s = sb.slot(MacGate::new());
            cs.resid.push((key, s));
        }
        880 => {
            let s = sb.slot(ResidualWeightsGate256::new());
            cs.resid.push((key, s));
        }
        884 => {
            let s = sb.slot(ResidualWeightsGate256::with_weights(
                ResidualWeightsGate256::N_WEIGHTS_WIDE,
            ));
            cs.resid.push((key, s));
        }
        881 => {
            let s = sb.slot(ResidualPrefix3Gate256::new());
            cs.resid.push((key, s));
        }
        882 => {
            let s = sb.slot(ResidualAccGate256::new());
            cs.resid.push((key, s));
        }
        311..=318 => {
            let s = sb.slot(PrefixGate::new(key - 310));
            cs.resid.push((key, s));
        }
        1001..=1008 => {
            let s = sb.slot(PrefixGate256::new(key - 1000));
            cs.resid.push((key, s));
        }
        _ => panic!("no envelope declaration for slot key {key}"),
    }
}

/// Asserts `a = b` by a MAC row `a + b` held to the assert-zero anchor, which never joins either
/// wire's class to the other's.
pub(super) fn emit_assert_eq(sb: &mut ShapeBuilder, macs: SlotId, k: Consts, a: Wire, b: Wire) {
    let t = sb.gate(macs, &[a, b, k.ow])[0];
    sb.connect(t, k.zassert);
}

/// The pad value the PoW-mask slot's padding rows check against.
fn pow_pad() -> F128 {
    F128::new(0, 1u64 << 63)
}

/// A circuit under construction to an envelope.
pub(super) struct EnvBuild {
    pub(super) sb: ShapeBuilder,
    pub(super) cs: ChildSlots,
    pub(super) k: Consts,
    pub(super) vals: Vec<F128>,
    pub(super) hints: Vec<[u32; SLOT_WORDS]>,
    pub(super) consts: Vec<(F128, Wire)>,
    /// The fixed public inputs, in public order.
    pub(super) fixed: Vec<Wire>,
    n_fixed: usize,
    n_le: usize,
    n_resid: usize,
}

impl EnvBuild {
    /// Starts a circuit: the base slots, the envelope's further slots, the three shared constants
    /// and the constant table, in that order.
    pub(super) fn begin(env: &HeadEnv, nu: usize, spread_w: usize) -> EnvBuild {
        let mut sb = ShapeBuilder::new(nu);
        let mut cs = ChildSlots::new_with_blake3_split(&mut sb, nu, spread_w, true);
        if !env.measure {
            for &key in &env.keys {
                declare(&mut sb, &mut cs, key);
            }
        }
        let mut vals = Vec::new();
        let k = Consts::new(&mut sb, &mut vals);
        let mut consts = vec![(F128::ZERO, k.zw), (F128::ONE, k.ow)];
        let mut fixed = vec![k.zw, k.ow, k.zassert];
        for &v in &env.table {
            assert!(
                v != F128::ZERO && v != F128::ONE,
                "the table holds the other constants"
            );
            vals.push(v);
            let w = sb.fixed_public_input(v);
            consts.push((v, w));
            fixed.push(w);
        }
        let n = consts.len();
        let w = cw(&mut sb, &mut vals, &mut consts, pow_pad());
        if consts.len() > n {
            fixed.push(w);
        }
        let n_fixed = consts.len();
        let (n_le, n_resid) = (cs.le.len(), cs.resid.len());
        EnvBuild {
            sb,
            cs,
            k,
            vals,
            hints: Vec::new(),
            consts,
            fixed,
            n_fixed,
            n_le,
            n_resid,
        }
    }

    /// Ends a circuit: records the constants it used, asserts each `deferred` pair equal, records
    /// its rows, pads the body, publishes the head block and pads every slot to its count. Padding
    /// stops where the circuit outgrows the envelope, which [`HeadEnv::holds`] then reports.
    pub(super) fn finish(
        &mut self,
        env: &HeadEnv,
        block: &[Wire],
        spread_w: usize,
        deferred: &[(Wire, Wire)],
    ) -> EnvCensus {
        let body = self.sb.public_len();
        let mut table: Vec<F128> = Vec::new();
        for &(v, w) in &self.consts {
            if v != F128::ZERO && v != F128::ONE && (v == pow_pad() || self.sb.wire_used(w)) {
                table.push(v);
            }
        }
        for &(a, b) in deferred {
            emit_assert_eq(&mut self.sb, self.cs.macs, self.k, a, b);
        }
        let counts: Vec<(usize, usize)> = slot_list(&self.cs)
            .iter()
            .map(|&(key, s)| (key, self.sb.rows_in_slot(s)))
            .collect();
        let census = EnvCensus {
            spread_w,
            counts,
            table,
            body,
            block: block.len(),
            layout: None,
        };
        let sb = &mut self.sb;
        if env.measure {
            for &w in block {
                sb.publish(w);
            }
            return census;
        }
        for _ in body..env.body {
            self.vals.push(F128::ZERO);
            sb.public_input();
        }
        for &w in block {
            sb.publish(w);
        }
        for _ in block.len()..env.block {
            sb.publish(self.k.zw);
        }
        let pow_w = self
            .consts
            .iter()
            .find(|&&(v, _)| v == pow_pad())
            .expect("the PoW pad constant")
            .1;
        for (key, s) in slot_list(&self.cs) {
            let Some(&(_, target)) = env.counts.iter().find(|&&(k2, _)| k2 == key) else {
                continue;
            };
            let live = sb.rows_in_slot(s);
            let zw = self.k.zw;
            let ins = if key == BASE_KEYS[4] {
                vec![zw, zw, zw, pow_w]
            } else {
                vec![zw; sb.slot_inputs(s)]
            };
            for _ in live..target {
                if key == BASE_KEYS[2] {
                    self.hints.push([0u32; SLOT_WORDS]);
                    sb.gate_hinted(s, &ins);
                } else {
                    sb.gate(s, &ins);
                }
            }
        }
        let _ = (self.n_fixed, self.n_le, self.n_resid);
        census
    }
}

impl HeadEnv {
    /// An envelope under which circuits are built unpadded, to measure themselves.
    pub fn measuring() -> HeadEnv {
        HeadEnv {
            measure: true,
            ..HeadEnv::default()
        }
    }

    /// An envelope under which circuits are built unpadded at `nu`, a size known to hold them.
    pub fn natural(nu: usize) -> HeadEnv {
        HeadEnv {
            nu,
            measure: true,
            ..HeadEnv::default()
        }
    }

    /// Whether a circuit built to this envelope with this census is the envelope's shape.
    pub fn holds(&self, c: &EnvCensus) -> bool {
        !self.measure
            && c.spread_w <= self.spread_w
            && c.body <= self.body
            && c.block <= self.block
            && c.counts
                .iter()
                .all(|&(k, n)| self.counts.iter().any(|&(k2, n2)| k2 == k && n <= n2))
            && c.table.iter().all(|v| self.table.contains(v))
            && (c.layout.is_none() || c.layout == self.layout)
    }

    /// The envelope grown to hold every census: row counts, body and block only grow, an
    /// outgrown count to a sixteenth over its census in steps of 64 rows, the body in steps of 256
    /// words, and the table is exactly the censuses' constants.
    pub fn grow(&self, census: &[&EnvCensus]) -> HeadEnv {
        let mut counts: Vec<(usize, usize)> = if self.measure {
            Vec::new()
        } else {
            self.counts.clone()
        };
        let mut table: Vec<F128> = Vec::new();
        for c in census {
            for &(k, n) in &c.counts {
                let room = (n + n / 16).next_multiple_of(64).max(1);
                match counts.iter_mut().find(|(k2, _)| *k2 == k) {
                    Some(e) if e.1 >= n => {}
                    Some(e) => e.1 = room,
                    None => counts.push((k, room)),
                }
            }
            for &v in &c.table {
                if !table.contains(&v) {
                    table.push(v);
                }
            }
        }
        counts.sort_by_key(|&(k, _)| k);
        table.sort_by_key(|v| (v.hi, v.lo));
        let max_rows = counts.iter().map(|&(_, n)| n).max().unwrap_or(1);
        let nu = (max_rows.next_power_of_two().trailing_zeros() as usize).max(7);
        let keys: Vec<usize> = counts
            .iter()
            .map(|&(k, _)| k)
            .filter(|k| !BASE_KEYS.contains(k))
            .collect();
        let body = census
            .iter()
            .map(|c| c.body)
            .max()
            .unwrap_or(0)
            .max(if self.measure { 0 } else { self.body })
            .next_multiple_of(256);
        HeadEnv {
            nu,
            spread_w: census
                .iter()
                .map(|c| c.spread_w)
                .max()
                .unwrap_or(0)
                .max(self.spread_w),
            keys,
            counts,
            table,
            body,
            block: census
                .iter()
                .map(|c| c.block)
                .max()
                .unwrap_or(0)
                .max(self.block),
            measure: false,
            layout: census
                .iter()
                .find_map(|c| c.layout.clone())
                .or_else(|| self.layout.clone()),
        }
    }
}

/// The transcript domain of every wrap and head proof.
pub(super) const ENV_DOMAIN: &[u8] = b"flock-rowmajor-wrap-v0";

#[derive(Clone, Copy)]
struct EnvSlots {
    b3: SlotId,
    b3_alt: SlotId,
    swap: SlotId,
    spread: SlotId,
    pow: SlotId,
    family: SlotId,
}

/// What a verifier of a wrap or head proof holds: the circuit, its commitment parameters and the
/// block circuits of its Boolean tables.
pub struct EnvKey {
    /// The circuit's shape.
    pub shape: Arc<CircuitShape>,
    /// The outer commitment's parameters.
    pub pcs: PcsParams,
    b3: Arc<BlockR1cs>,
    swap: BlockR1cs,
    spread: BlockR1cs,
    pow: BlockR1cs,
    family: BlockR1cs,
    slots: EnvSlots,
    nu: usize,
    spread_w: usize,
}

/// A wrap or head proof: the outer union-circuit proof, its commitment and the circuit's public
/// segment.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct EnvProof {
    /// The outer proof.
    pub proof: R1csProofCircuitMerged,
    /// The outer commitment.
    pub commitment: Commitment,
    /// The public segment.
    pub public: Vec<F128>,
}

/// Phase timings of building and proving one circuit, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct EnvTimings {
    /// Building the circuit shape.
    pub build: f64,
    /// Running the witness.
    pub witness: f64,
    /// Proving the circuit.
    pub prove: f64,
}

impl EnvKey {
    fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
        let s = &self.shape;
        let mut lco: Vec<(usize, &dyn LincheckCircuit)> = vec![
            (
                s.registry_slot(self.slots.b3),
                self.b3.csc_lincheck_circuit(),
            ),
            (
                s.registry_slot(self.slots.b3_alt),
                self.b3.csc_lincheck_circuit(),
            ),
            (
                s.registry_slot(self.slots.swap),
                self.swap.csc_lincheck_circuit(),
            ),
            (
                s.registry_slot(self.slots.spread),
                self.spread.csc_lincheck_circuit(),
            ),
            (
                s.registry_slot(self.slots.pow),
                self.pow.csc_lincheck_circuit(),
            ),
            (
                s.registry_slot(self.slots.family),
                self.family.csc_lincheck_circuit(),
            ),
        ];
        lco.sort_by_key(|(i, _)| *i);
        lco.into_iter().map(|(_, c)| c).collect()
    }

    /// The Boolean tables' matrices, in registry order.
    pub(super) fn boolean_mats(&self) -> Vec<(&SparseBinaryMatrix, &SparseBinaryMatrix)> {
        let s = &self.shape;
        let mut v = vec![
            (s.registry_slot(self.slots.b3), (&self.b3.a_0, &self.b3.b_0)),
            (
                s.registry_slot(self.slots.b3_alt),
                (&self.b3.a_0, &self.b3.b_0),
            ),
            (
                s.registry_slot(self.slots.swap),
                (&self.swap.a_0, &self.swap.b_0),
            ),
            (
                s.registry_slot(self.slots.spread),
                (&self.spread.a_0, &self.spread.b_0),
            ),
            (
                s.registry_slot(self.slots.pow),
                (&self.pow.a_0, &self.pow.b_0),
            ),
            (
                s.registry_slot(self.slots.family),
                (&self.family.a_0, &self.family.b_0),
            ),
        ];
        v.sort_by_key(|(i, _)| *i);
        v.into_iter().map(|(_, m)| m).collect()
    }

    /// The Boolean tables' lincheck circuits, in registry order.
    pub(super) fn boolean_lcs(&self) -> Vec<&dyn LincheckCircuit> {
        self.lincheck_circuits()
    }

    /// The log row capacity of every slot.
    pub fn nu(&self) -> usize {
        self.nu
    }

    /// The circuit's digest.
    pub fn digest(&self) -> [u8; 32] {
        self.shape.circuit.digest()
    }

    /// A proof under this key in the form the head walker reads.
    pub(super) fn leaf_outer(&self, proof: &EnvProof) -> LeafOuter {
        let s = &self.shape;
        LeafOuter {
            shape: self.shape.clone(),
            public: proof.public.clone(),
            proof: MixedProof::Rs(proof.proof.clone()),
            commitment: proof.commitment.clone(),
            pcs: self.pcs.clone(),
            b3_r1cs: self.b3.clone(),
            swap_r1cs: SwapTable::build_block_r1cs(self.nu),
            spread_r1cs: BitSpreadTable::new(self.spread_w).build_block_r1cs(self.nu),
            pow_r1cs: PowMaskTable.build_block_r1cs(self.nu),
            family_r1cs: FamilyTransposeTileTable::build_block_r1cs(self.nu),
            b3_slots: vec![
                s.registry_slot(self.slots.b3),
                s.registry_slot(self.slots.b3_alt),
            ],
            swap_slot: s.registry_slot(self.slots.swap),
            spread_slot: s.registry_slot(self.slots.spread),
            pow_slot: s.registry_slot(self.slots.pow),
            family_slot: s.registry_slot(self.slots.family),
        }
    }

    /// Verifies a proof under this key, opened through `outer` (Ligerito when `None`).
    pub fn verify(
        &self,
        proof: &EnvProof,
        outer: Option<&dyn OuterPcs>,
    ) -> Result<(), FlockVerifyError> {
        let union = UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
        let lcs = self.lincheck_circuits();
        verify_union_circuit_with_outer(
            &union,
            &self.shape.circuit,
            &proof.public,
            &lcs,
            &proof.commitment,
            &proof.proof,
            &self.pcs,
            outer,
            &mut FsChallenger::with_chained_blake3(ENV_DOMAIN),
        )
        .map(|_| ())
    }
}

/// Finishes the circuit `eb` built at `nu`, runs its witness, hands the public segment to `check`,
/// and proves it with `outer` (Ligerito when `None`).
pub(super) fn prove_env(
    eb: EnvBuild,
    nu: usize,
    spread_w: usize,
    outer: Option<&dyn OuterPcs>,
    check: impl FnOnce(&[F128]),
) -> (EnvKey, EnvProof, EnvTimings) {
    let mut timings = EnvTimings::default();
    let t0 = Instant::now();
    let EnvBuild {
        sb,
        cs,
        vals,
        hints,
        ..
    } = eb;
    let q = cs.q;
    let slots = EnvSlots {
        b3: q.b3,
        b3_alt: q.b3_alt.expect("the second BLAKE3 slot"),
        swap: q.swap,
        spread: q.spread,
        pow: q.pow,
        family: q.family.expect("the family-H slot"),
    };
    let shape = sb.finish().expect("the circuit builds");
    timings.build = t0.elapsed().as_secs_f64();
    let t0 = Instant::now();
    let hint_refs: Vec<&(dyn Any + Sync)> = hints.iter().map(|h| h as &(dyn Any + Sync)).collect();
    let fill_plan = shape.fill_plan();
    let mut witness = shape.run_filled_deferred(&fill_plan, &vals, &hint_refs);
    check(&witness.public);
    timings.witness = t0.elapsed().as_secs_f64();
    let dense_m = UnionInstance::new(&shape.registry, shape.counts.clone()).dense_m();
    let pf = LigeritoProfile::Fast;
    let pcs = PcsParams {
        m: dense_m,
        log_inv_rate: pf.log_inv_rate(),
        log_batch_size: embedded_initial_k_or_default(dense_m, pf),
        profile: pf,
        num_lanes: None,
        merkle_hash: HashKind::Blake3,
    };
    let key = EnvKey {
        b3: chain_blake_r1cs(nu),
        swap: SwapTable::build_block_r1cs(nu),
        spread: BitSpreadTable::new(spread_w).build_block_r1cs(nu),
        pow: PowMaskTable.build_block_r1cs(nu),
        family: FamilyTransposeTileTable::build_block_r1cs(nu),
        slots,
        nu,
        spread_w,
        pcs,
        shape: Arc::new(shape),
    };
    let t0 = Instant::now();
    let s = &key.shape;
    let union = UnionInstance::new(&s.registry, s.counts.clone());
    let b3_rows = witness.rows::<Blake3Gate>(slots.b3).to_vec();
    let b3_alt_rows = witness.rows::<Blake3Gate>(slots.b3_alt).to_vec();
    let swap_rows = witness.rows::<SwapGate>(slots.swap).to_vec();
    let spread_rows = witness.rows::<BitSpreadGate>(slots.spread).to_vec();
    let pow_rows = witness.rows::<PowMaskGate>(slots.pow).to_vec();
    let family_rows = witness
        .rows::<FamilyTransposeTileGate>(slots.family)
        .to_vec();
    let spread_ty = BitSpreadTable::new(spread_w);
    let mut bslots: Vec<(usize, UnionSlotProverInput)> = vec![
        (
            s.registry_slot(slots.swap),
            UnionSlotProverInput::in_place(
                move |dst| SwapTable::generate_witness_batch_major_into(&swap_rows, dst),
                key.swap.csc_lincheck_circuit(),
            ),
        ),
        (
            s.registry_slot(slots.spread),
            UnionSlotProverInput::in_place(
                move |dst| spread_ty.generate_witness_batch_major_into(&spread_rows, dst),
                key.spread.csc_lincheck_circuit(),
            ),
        ),
        (
            s.registry_slot(slots.pow),
            UnionSlotProverInput::in_place(
                move |dst| PowMaskTable.generate_witness_batch_major_into(&pow_rows, dst),
                key.pow.csc_lincheck_circuit(),
            ),
        ),
        (
            s.registry_slot(slots.family),
            UnionSlotProverInput::in_place(
                move |dst| {
                    FamilyTransposeTileTable::generate_witness_batch_major_into(&family_rows, dst)
                },
                key.family.csc_lincheck_circuit(),
            ),
        ),
        (
            s.registry_slot(slots.b3),
            UnionSlotProverInput::in_place(
                move |dst| generate_witness_batch_major_partial_into(&b3_rows, nu, dst),
                key.b3.csc_lincheck_circuit(),
            ),
        ),
        (
            s.registry_slot(slots.b3_alt),
            UnionSlotProverInput::in_place(
                move |dst| generate_witness_batch_major_partial_into(&b3_alt_rows, nu, dst),
                key.b3.csc_lincheck_circuit(),
            ),
        ),
    ];
    bslots.sort_by_key(|(i, _)| *i);
    let mut el_ord: Vec<(usize, Vec<Vec<F128>>)> = cs
        .element_slot_ids()
        .into_iter()
        .map(|sl| (s.registry_slot(sl), witness.take_rows_of::<Vec<F128>>(sl)))
        .collect();
    el_ord.sort_by_key(|(i, _)| *i);
    let el_inputs = el_ord
        .into_iter()
        .map(|(_, rows)| live_element_input_from_rows(rows, nu))
        .collect();
    let (proof, commitment, _) = prove_union_circuit_with_outer(
        &union,
        &s.circuit,
        &witness.public,
        &key.pcs,
        bslots.into_iter().map(|(_, x)| x).collect(),
        el_inputs,
        outer,
        &mut FsChallenger::with_chained_blake3(ENV_DOMAIN),
    );
    timings.prove = t0.elapsed().as_secs_f64();
    let public = witness.public;
    (
        key,
        EnvProof {
            proof,
            commitment,
            public,
        },
        timings,
    )
}
