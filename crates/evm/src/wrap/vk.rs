// SPDX-License-Identifier: LGPL-3.0-or-later

//! What the contract holds of a wrapped lift's shape: the constants of the wrap circuit, of its
//! commitment and of the fixed tables' commitment, as plain data.

use flock_prover::{
    circuit::CellSlot,
    field::F128,
    union::UnionInstance,
};
use pofseed_flock_lift::{wrap::words_at, wrapped::WrappedKey};
use pofseed_flock_lift_structure::key::StructVk;
use pofseed_flock_lift_whir::params::Config;

/// A Boolean table type of the wrap circuit.
#[derive(Clone, Debug)]
pub struct BoolType {
    /// log2 of the type's rows and columns.
    pub k_log: usize,
    /// The slot's prefix over the Boolean region's high coordinates.
    pub prefix: usize,
    /// The column pinned to the constant wire.
    pub pin: Option<usize>,
    /// Declared rows.
    pub count: usize,
    /// The committed table the type's matrices are.
    pub table: usize,
}

/// A sparse matrix over the field, by rows of `(column, coefficient)`.
pub type Sparse = Vec<Vec<(usize, F128)>>;

/// An element table type of the wrap circuit.
#[derive(Clone, Debug)]
pub struct ElemType {
    /// log2 of the type's columns.
    pub kappa: usize,
    /// The slot's prefix over the element region's high column coordinates.
    pub prefix: usize,
    /// The `A` matrix.
    pub a: Sparse,
    /// The `B` matrix.
    pub b: Sparse,
    /// The `A` side's affine constants.
    pub a_const: Vec<F128>,
    /// The `B` side's affine constants.
    pub b_const: Vec<F128>,
}

/// A run of layout columns sharing one pair of cumulative heights.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Run {
    /// The cumulative height before the run's columns.
    pub t0: u64,
    /// The cumulative height after one of them.
    pub t1: u64,
    /// The run's first column.
    pub start: usize,
    /// Columns in the run.
    pub len: usize,
}

/// The constants of a wrapped lift's verifier.
#[derive(Clone, Debug)]
pub struct Vk {
    /// log2 of the circuit's rows.
    pub nu: usize,
    /// Variables of the Boolean region.
    pub m_bool: usize,
    /// Variables of the whole address space.
    pub m_total: usize,
    /// Variables of the element region.
    pub m_elem: usize,
    /// log2 of the committed stack's words.
    pub dense_log: usize,
    /// log2 of the layout's columns.
    pub k_cols: usize,
    /// log2 of the cells.
    pub mu: usize,
    /// Proof-of-work bits before the wiring argument's fingerprint challenge.
    pub gkr_bits: u32,
    /// The registry's digest.
    pub registry_digest: [u8; 32],
    /// The declared counts, eight little-endian bytes each.
    pub counts_le: Vec<u8>,
    /// The circuit's digest.
    pub circuit_digest: [u8; 32],
    /// The fixed prefix of the public segment.
    pub fixed: Vec<F128>,
    /// Words of the public segment.
    pub num_public: usize,
    /// The Boolean table types.
    pub bools: Vec<BoolType>,
    /// Committed tables.
    pub n_tables: usize,
    /// The element table types.
    pub elems: Vec<ElemType>,
    /// The element region's frozen high word coordinates.
    pub elem_frozen: Vec<bool>,
    /// Per gate cell slot, the layout column it reads.
    pub gate_cols: Vec<usize>,
    /// The boundary runs of the layout.
    pub runs: Vec<Run>,
    /// Per chunk, where its published words sit in the public segment, and their number.
    pub words: Vec<(usize, usize)>,
    /// Where the accumulated claims on the block's `A` and `B` sit: offset, column and row variables.
    pub acc: [(usize, usize, usize); 2],
    /// The outer commitment's parameters.
    pub whir: Config,
    /// The fixed tables' commitment.
    pub structure: StructVk,
    /// Responses per lift.
    pub responses: usize,
    /// Responses per chunk.
    pub chunk: usize,
    /// Published words per response.
    pub n_io: usize,
    /// The expected output's word counts, packed as the contracts take them.
    pub counts: u64,
}

impl Vk {
    /// The constants of lifts under `key`, whose outer commitment has parameters `whir`, of a
    /// statement whose expected output has the word counts `counts`.
    pub fn new(key: &WrappedKey, whir: Config, n_io: usize, counts: u64) -> Self {
        let env = &key.wrap.key;
        let shape = &env.shape;
        let registry = &shape.registry;
        let union = UnionInstance::new(registry, shape.counts.clone());
        let nu = registry.nu();
        let cells = shape.circuit.cells();
        let table_of = &key.root.table_of;
        let bools = registry
            .boolean_types()
            .iter()
            .zip(registry.slots())
            .zip(&shape.counts)
            .zip(table_of)
            .map(|(((ty, slot), &count), &table)| BoolType {
                k_log: ty.k_log,
                prefix: slot.prefix,
                pin: ty.const_pin,
                count,
                table,
            })
            .collect();
        let sparse = |m: &flock_prover::element_r1cs::SparseF128Matrix| -> Sparse { m.rows.clone() };
        let elems = registry
            .element_types()
            .iter()
            .zip(union.element_slot_layout())
            .map(|(ty, layout)| {
                let e = ty.element_type().expect("an element type");
                ElemType {
                    kappa: layout.kappa,
                    prefix: layout.region_prefix(nu),
                    a: sparse(e.a_0()),
                    b: sparse(e.b_0()),
                    a_const: e.a_const().to_vec(),
                    b_const: e.b_const().to_vec(),
                }
            })
            .collect();
        let zeros = vec![F128::ZERO; nu];
        let gate_cols = (0..cells.num_gate_slots())
            .map(|iota| {
                cells.gate_claim_point(iota, &zeros)[nu..]
                    .iter()
                    .enumerate()
                    .fold(0usize, |acc, (i, &b)| acc | ((b == F128::ONE) as usize) << i)
            })
            .collect();
        assert_eq!(cells.num_public_slots(), 1, "the public segment fits one cell slot");
        assert!(matches!(cells.slots()[cells.num_gate_slots()], CellSlot::Public { s: 0 }));
        let heights = union.jagged_heights();
        assert!(flock_prover::pcs::jagged::rectangular_prefix_columns(&heights, nu).is_none(), "a jagged stack");
        let mut runs: Vec<Run> = Vec::new();
        let mut t = 0u64;
        for (y, &h) in heights.iter().enumerate() {
            match runs.last_mut() {
                Some(run) if run.t0 == t && run.t1 == t + h => run.len += 1,
                _ => runs.push(Run { t0: t, t1: t + h, start: y, len: 1 }),
            }
            t += h;
        }
        let fixed_public = shape.circuit.fixed_public();
        let n_fixed = fixed_public.iter().take_while(|f| f.is_some()).count();
        assert!(fixed_public[n_fixed..].iter().all(Option::is_none), "the fixed public words are a prefix");
        let acc = [0, 1].map(|i| key.wrap.acc[i]);
        return Self {
            nu,
            m_bool: registry.m_bool(),
            m_total: registry.m_total(),
            m_elem: registry.m_elem(),
            dense_log: env.pcs.m - 7,
            k_cols: union.col_log(),
            mu: cells.mu(),
            gkr_bits: flock_prover::challenger::grinding_bits_for_degree(
                shape.circuit.live_mask().counts.iter().sum::<usize>().saturating_sub(1),
            )
            .max(1),
            registry_digest: registry.digest(),
            counts_le: shape.counts.iter().flat_map(|&n| (n as u64).to_le_bytes()).collect(),
            circuit_digest: shape.circuit.digest(),
            fixed: fixed_public[..n_fixed].iter().map(|f| f.expect("fixed")).collect(),
            num_public: shape.circuit.num_public(),
            bools,
            n_tables: table_of.iter().max().map_or(0, |m| m + 1),
            elems,
            elem_frozen: union.element_prefix_coords().iter().map(|&c| c == F128::ONE).collect(),
            gate_cols,
            runs,
            words: (0..key.wrap.tails.len()).map(|i| words_at(&key.wrap, i)).collect(),
            acc,
            whir,
            structure: key.root.structure.verifying(),
            responses: key.responses,
            chunk: key.chunk,
            counts,
            n_io,
        };
    }

    /// Whether word `i` of the public segment is one of a chunk's published words.
    pub fn is_published(&self, i: usize) -> bool {
        return self.words.iter().any(|&(at, len)| (at..at + len).contains(&i));
    }

    /// Live responses of chunk `c`.
    pub fn live(&self, c: usize) -> usize {
        return self.chunk.min(self.responses - c * self.chunk);
    }

    /// The public cell slot.
    pub fn public_slot(&self) -> usize {
        return self.gate_cols.len();
    }
}
