// SPDX-License-Identifier: LGPL-3.0-or-later

//! The proof that claimed evaluations of the fixed tables are the committed tables'.
//!
//! The claims are of four kinds: the block's two constraint matrices at a point each; every
//! Boolean table type's two matrices under the weights a lincheck leaves; and the wrap circuit's
//! live mask, masked identity and wiring permutation at one point. The table claims are first
//! folded to a point each. Four sumchecks then reduce everything to evaluations of the committed
//! bytes' bits, which one opening discharges:
//!
//! - over the block's operations and their row masks, for the block claims' explicit part;
//! - over the Keccak tensor, for the block claims' shared Keccak-f part;
//! - over the live cells;
//! - over the small table types' entries.

use flock_prover::{
    challenger::Challenger,
    field::{F128, F256},
    lincheck::build_eq_table,
    matrix_fold::{FoldGrinding, FoldMatrix, FoldProof, MatrixClaim, prove_fold_with_grinding, verify_fold_with_grinding},
};
use pofseed_flock_lift_block::{kernel::WORD_LOG, program::product_range_sum};
use pofseed_flock_lift_whir::whir;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::{
    adder::rotated_eq,
    key::{Held, KERNEL_LOG, Layout, OP_BITS, Region, StructKey, StructVk, WORD_BITS},
    subfield::{DEGREE, are_conjugates, bit_value, conjugates},
    sumcheck::{self, Rounds, Term, eq},
};

/// Bits of a word's bit index.
const LOW: usize = 6;

/// An evaluation claim on one of the block's matrices: the row point, the column point, the value.
pub type PointClaim = (Vec<F128>, Vec<F128>, F128);

/// The claims a structure proof discharges.
#[derive(Clone, Debug)]
pub struct Claims {
    /// The block's `A` and `B` matrices at a point each.
    pub block: [PointClaim; 2],
    /// Per table, the claims on `A` and on `B` of every table type that shares it.
    pub tables: Vec<[Vec<MatrixClaim>; 2]>,
    /// The wiring point, and the live mask, the masked identity and the wiring permutation there.
    pub cells: (Vec<F128>, [F128; 3]),
}

/// A structure proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StructProof {
    /// Per table, the folds of its `A` and of its `B` claims.
    pub folds: Vec<[FoldProof; 2]>,
    /// The Keccak tensor's share of each block claim, before the sub-blocks' weight.
    pub kernel_values: [F128; 2],
    /// The nonce ground before the batching coefficients.
    pub batching_nonce: u64,
    /// The operations sumcheck over a row's bits.
    pub ops_bits_rounds: Rounds,
    /// The operations sumcheck over the operations.
    pub ops_rounds: Rounds,
    /// The masks' extension at the sumcheck's point.
    pub mask: F128,
    /// The descriptors' bits at the sumcheck's point.
    pub ops: Vec<F128>,
    /// The Keccak tensor's sumcheck.
    pub kernel_rounds: Rounds,
    /// The tensor's extension at the sumcheck's point.
    pub kernel: F128,
    /// The live cells' sumcheck.
    pub cells_rounds: Rounds,
    /// The cell entries' bits at the sumcheck's point.
    pub cells: Vec<F128>,
    /// The small entries' sumcheck.
    pub small_rounds: Rounds,
    /// The small entries' bits at the sumcheck's point.
    pub small: Vec<F128>,
    /// The nonce ground before the bit-batching points.
    pub bits_nonce: u64,
    /// Per bit claim, the square roots of its point, seven deep.
    pub roots: Vec<Vec<Vec<F128>>>,
    /// Per bit claim, the bytes' extension at the point and at its seven roots.
    pub values: Vec<Vec<F128>>,
    /// The opening of the committed bytes at every such point.
    pub opening: whir::Proof,
}

/// Why a structure proof was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructError {
    /// The claims or the proof do not have the layout's shape.
    Shape,
    /// A table claim's fold was refused.
    Fold,
    /// A proof-of-work nonce is invalid.
    Grinding,
    /// The operations sumcheck does not close.
    Operations,
    /// The Keccak tensor's sumcheck does not close.
    Kernel,
    /// The live cells' sumcheck does not close.
    Cells,
    /// The small entries' sumcheck does not close.
    Small,
    /// A point's claimed roots are not its roots.
    Roots,
    /// A claimed evaluation of bits is not what the bytes' evaluations give.
    Bits,
    /// The opening was refused.
    Opening,
}

/// What a block claim contributes to the sumchecks, on one side.
struct Side {
    /// The row point's bit coordinates.
    a: Vec<F128>,
    /// The column point's bit coordinates.
    b: Vec<F128>,
    /// The row point's word coordinates, padded to a descriptor's.
    xr: Vec<F128>,
    /// The column point's word coordinates, padded to a descriptor's.
    xc: Vec<F128>,
    /// The sub-blocks' weight on the Keccak tensor.
    weight: F128,
    /// The weight of a Keccak row's read of the constant wire.
    constant: F128,
}

fn padded(point: &[F128], n: usize) -> Vec<F128> {
    let mut p = point.to_vec();
    p.resize(n, F128::ZERO);
    return p;
}

impl Side {
    fn new(layout: &Layout, row: &[F128], col: &[F128]) -> Option<Side> {
        if row.len() != layout.k_log || col.len() != layout.k_log || layout.k_log < LOW + WORD_LOG {
            return None;
        }
        let (rh, ch) = (&row[LOW + WORD_LOG..], &col[LOW + WORD_LOG..]);
        let range = (layout.head_subs, layout.head_subs + layout.keccak_subs);
        let both: Vec<(F128, F128)> = rh.iter().zip(ch).map(|(&p, &q)| ((F128::ONE + p) * (F128::ONE + q), p * q)).collect();
        let rows: Vec<(F128, F128)> = rh.iter().map(|&p| (F128::ONE + p, p)).collect();
        let at_constant = col.iter().fold(F128::ONE, |acc, &c| acc * (F128::ONE + c));
        return Some(Side {
            a: row[..LOW].to_vec(),
            b: col[..LOW].to_vec(),
            xr: padded(&row[LOW..], WORD_BITS),
            xc: padded(&col[LOW..], WORD_BITS),
            weight: product_range_sum(&both, range.0, range.1),
            constant: product_range_sum(&rows, range.0, range.1) * at_constant,
        });
    }
}

/// The operations sumcheck's term over the operations, after the row's bits are bound to `tau`:
/// the columns are the mask, then the descriptor's bits.
struct OpsTerm<'a> {
    sides: &'a [Side; 2],
    mu: [F128; 2],
    tau: &'a [F128],
}

impl OpsTerm<'_> {
    /// The factor a side contributes at a descriptor's bits, without the mask.
    fn side(&self, s: usize, bits: &[F128]) -> F128 {
        let side = &self.sides[s];
        let select = if s == 0 { F128::ONE + bits[1] } else { bits[1] };
        if select == F128::ZERO {
            return F128::ZERO;
        }
        let (kc, fixed, shift) = (bits[0], bits[2], &bits[3..9]);
        let (row, col) = (&bits[9..9 + WORD_BITS], &bits[9 + WORD_BITS..9 + 2 * WORD_BITS]);
        let mut acc = F128::ZERO;
        if kc != F128::ONE {
            let read = fixed * eq(&side.b, shift) + (F128::ONE + fixed) * rotated_eq(self.tau, shift, &side.b);
            acc += (F128::ONE + kc) * eq(&side.xr, row) * eq(&side.xc, col) * read;
        }
        if kc != F128::ZERO {
            acc += kc * eq(&side.xr[..WORD_LOG], &row[..WORD_LOG]) * side.constant;
        }
        return self.mu[s] * eq(&side.a, self.tau) * select * acc;
    }
}

impl Term for OpsTerm<'_> {
    fn degree(&self) -> usize {
        return OP_BITS + 1;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        if row[0] == F128::ZERO {
            return F128::ZERO;
        }
        return row[0] * (self.side(0, &row[1..]) + self.side(1, &row[1..]));
    }
}

/// The operations sumcheck's term over a row's bits: per group of operations, the masks' weighted
/// sum, the side's row weight and the group's column weight.
struct RowTerm {
    groups: usize,
}

/// Groups of operations per side: one per shift, the fixed operations, and the constant reads.
const GROUPS: usize = 66;

impl Term for RowTerm {
    fn degree(&self) -> usize {
        return 3;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        // Columns: the groups' sums, the two sides' row weights, then each side's column weight per shift.
        let g = self.groups;
        let mut acc = F128::ZERO;
        for s in 0..2 {
            let mut side = F128::ZERO;
            for j in 0..GROUPS {
                let sum = row[s * GROUPS + j];
                if sum != F128::ZERO {
                    side += if j < 64 { sum * row[g + 2 + s * 64 + j] } else { sum };
                }
            }
            acc += side * row[g + s];
        }
        return acc;
    }
}

struct CellsTerm<'a> {
    mu: usize,
    rho: &'a [F128],
    c: [F128; 3],
}

fn embedded(bits: &[F128]) -> F128 {
    return bits.iter().enumerate().fold(F128::ZERO, |acc, (i, &b)| acc + b * F128::new(1 << i, 0));
}

impl Term for CellsTerm<'_> {
    fn degree(&self) -> usize {
        return self.mu + 2;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        if row[0] == F128::ZERO {
            return F128::ZERO;
        }
        let (x, sigma) = (&row[1..1 + self.mu], &row[1 + self.mu..1 + 2 * self.mu]);
        return row[0] * eq(self.rho, x) * (self.c[0] + self.c[1] * embedded(x) + self.c[2] * embedded(sigma));
    }
}

/// A folded claim on a small table's matrix: its identifier's bits, its points and its coefficient.
struct SmallClaim {
    id: Vec<F128>,
    row: Vec<F128>,
    col: Vec<F128>,
    coefficient: F128,
}

struct SmallTerm<'a> {
    id: usize,
    index: usize,
    claims: &'a [SmallClaim],
}

impl Term for SmallTerm<'_> {
    fn degree(&self) -> usize {
        return 1 + self.id + 2 * self.index;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        if row[0] == F128::ZERO {
            return F128::ZERO;
        }
        let (id, r, c) = (&row[1..1 + self.id], &row[1 + self.id..1 + self.id + self.index], &row[1 + self.id + self.index..]);
        let sum = self
            .claims
            .iter()
            .fold(F128::ZERO, |acc, k| acc + k.coefficient * eq(&k.id, id) * eq(&k.row, r) * eq(&k.col, c));
        return row[0] * sum;
    }
}

struct Product;

impl Term for Product {
    fn degree(&self) -> usize {
        return 2;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        return row[0] * row[1];
    }
}

/// The Keccak tensor's weight at a point over its offset, column word, row word and side.
fn kernel_weight(sides: &[Side; 2], mu: [F128; 2], theta: &[F128]) -> F128 {
    let (d, w2, w, s) = (&theta[..LOW], &theta[LOW..LOW + WORD_LOG], &theta[LOW + WORD_LOG..LOW + 2 * WORD_LOG], theta[KERNEL_LOG - 1]);
    return (0..2).fold(F128::ZERO, |acc, i| {
        let side = &sides[i];
        let select = if i == 0 { F128::ONE + s } else { s };
        acc + mu[i] * select * eq(&side.xr[..WORD_LOG], w) * eq(&side.xc[..WORD_LOG], w2) * rotated_eq(&side.a, d, &side.b)
    });
}

fn bit_columns(slots: &[u64], bits: usize) -> Vec<Vec<F128>> {
    return (0..bits)
        .into_par_iter()
        .map(|i| slots.iter().map(|&s| if s >> i & 1 == 1 { F128::ONE } else { F128::ZERO }).collect())
        .collect();
}

fn bit_point(i: usize, n: usize) -> Vec<F128> {
    return (0..n).map(|j| if i >> j & 1 == 1 { F128::ONE } else { F128::ZERO }).collect();
}

/// `Σ_i eq(zeta, i)·bits[i]`: the extension of a list's bits at a point over the bit index.
fn batched(zeta: &[F128], bits: &[F128]) -> F128 {
    return build_eq_table(zeta).iter().zip(bits).fold(F128::ZERO, |acc, (&e, &b)| acc + e * b);
}

/// A claim on the committed bytes' bits: the point and the value.
type BitClaim = (Vec<F128>, F128);

fn list_claim(region: Region, n: usize, zeta: &[F128], point: &[F128], bits: &[F128]) -> BitClaim {
    let local: Vec<F128> = zeta.iter().chain(point).copied().collect();
    return (region.lift(&local, n), batched(zeta, bits));
}

/// The small tables' folded claims, with coefficients, and the dense tables' as bit claims.
fn split_tables(layout: &Layout, folded: &[[MatrixClaim; 2]], coefficients: &[F128]) -> (Vec<SmallClaim>, Vec<BitClaim>, F128) {
    let (mut small, mut dense, mut target) = (Vec::new(), Vec::new(), F128::ZERO);
    for (&(k, held), claims) in layout.tables.iter().zip(folded) {
        for (side, claim) in claims.iter().enumerate() {
            match held {
                Held::Dense(regions) => {
                    let local: Vec<F128> = claim.col.point.iter().chain(&claim.row.point).copied().collect();
                    debug_assert_eq!(local.len(), 2 * k);
                    dense.push((regions[side].lift(&local, layout.n), claim.value));
                }
                Held::Small(id) => {
                    let coefficient = coefficients[small.len()];
                    target += coefficient * claim.value;
                    small.push(SmallClaim {
                        id: bit_point(id + side, layout.small_id),
                        row: padded(&claim.row.point, layout.small_index),
                        col: padded(&claim.col.point, layout.small_index),
                        coefficient,
                    });
                }
            }
        }
    }
    return (small, dense, target);
}

fn small_count(layout: &Layout) -> usize {
    return 2 * layout.tables.iter().filter(|(_, h)| matches!(h, Held::Small(_))).count();
}

fn bind<Ch: Challenger>(claims: &Claims, ch: &mut Ch) {
    ch.observe_label(b"pofseed-flock-lift-structure-v1");
    for (row, col, value) in &claims.block {
        ch.observe_f128_slice(row);
        ch.observe_f128_slice(col);
        ch.observe_f128(*value);
    }
    ch.observe_f128_slice(&claims.cells.0);
    ch.observe_f128_slice(&claims.cells.1);
}

/// Proves `claims` about the tables of `key`.
pub fn prove<Ch: Challenger>(key: &StructKey, claims: &Claims, ch: &mut Ch) -> StructProof {
    let layout = &key.layout;
    let timing = std::env::var_os("POFSEED_TIMING").is_some();
    let mut t = std::time::Instant::now();
    let mut lap = |what: &str| {
        if timing {
            eprintln!("[pofseed] structure: {what} {:.2} s", t.elapsed().as_secs_f64());
        }
        t = std::time::Instant::now();
    };
    bind(claims, ch);
    assert_eq!(claims.tables.len(), key.tables.len());
    let mut folds = Vec::with_capacity(key.tables.len());
    let mut folded = Vec::with_capacity(key.tables.len());
    for (table, groups) in key.tables.iter().zip(&claims.tables) {
        let fold = |m: &dyn FoldMatrix, group: &[MatrixClaim], ch: &mut Ch| {
            let combs: Vec<Vec<F128>> = group.iter().map(|c| m.col_marginal(&c.row.materialize(), 1 << table.k_log)).collect();
            prove_fold_with_grinding(m, &combs, group, FoldGrinding::per_challenge_128(), ch)
        };
        let (pa, ca) = fold(&table.a, &groups[0], ch);
        let (pb, cb) = fold(&table.b, &groups[1], ch);
        folds.push([pa, pb]);
        folded.push([ca, cb]);
    }
    lap("table folds");
    let sides = [0, 1].map(|s| Side::new(layout, &claims.block[s].0, &claims.block[s].1).expect("block claims of the layout's shape"));
    let pairing: [Vec<F128>; 2] = [0, 1].map(|s| {
        let (a, b) = (build_eq_table(&sides[s].a), build_eq_table(&sides[s].b));
        (0..64).map(|d| (0..64).fold(F128::ZERO, |acc, z| acc + a[z] * b[(z + d) % 64])).collect()
    });
    let words: [(Vec<F128>, Vec<F128>); 2] =
        [0, 1].map(|s| (build_eq_table(&sides[s].xr[..WORD_LOG]), build_eq_table(&sides[s].xc[..WORD_LOG])));
    let mut kernel_values = [F128::ZERO; 2];
    for &(side, w, w2, mask) in &key.kernel.words {
        let s = side as usize;
        let offsets = (0..64).filter(|d| mask >> d & 1 == 1).fold(F128::ZERO, |acc, d| acc + pairing[s][d]);
        kernel_values[s] += words[s].0[w as usize] * words[s].1[w2 as usize] * offsets;
    }
    ch.observe_f128_slice(&kernel_values);
    let n_small = small_count(layout);
    let (batching_nonce, coefficients) = ch.grind_pow_and_sample_f128_vec(1, 7 + n_small);
    let (mu, nu, cc) = ([coefficients[0], coefficients[1]], [coefficients[2], coefficients[3]], [coefficients[4], coefficients[5], coefficients[6]]);

    // The operations sumcheck: a row's bits first, then the operations.
    let descriptors = key.slots(layout.ops);
    let masks = key.slots(layout.masks);
    let row_tables: [(Vec<F128>, Vec<F128>); 2] = [0, 1].map(|s| {
        let live = layout.k_log - LOW;
        (build_eq_table(&sides[s].xr[..live]), build_eq_table(&sides[s].xc[..live]))
    });
    let shift_tables: [Vec<F128>; 2] = [0, 1].map(|s| build_eq_table(&sides[s].b));
    let n_groups = 2 * GROUPS;
    let sums = descriptors
        .par_chunks(1 << 12)
        .zip(masks.par_chunks(1 << 12))
        .map(|(ds, ms)| {
            let mut acc = vec![[F128::ZERO; 64]; n_groups];
            for (&d, &mask) in ds.iter().zip(ms) {
                if mask == 0 {
                    continue;
                }
                let s = (d >> 1 & 1) as usize;
                let (kc, fixed, shift) = (d & 1 == 1, d >> 2 & 1 == 1, (d >> 3 & 63) as usize);
                let (row, col) = ((d >> 9) as usize & ((1 << WORD_BITS) - 1), (d >> (9 + WORD_BITS)) as usize & ((1 << WORD_BITS) - 1));
                let (group, coefficient) = if kc {
                    (65, words[s].0[row] * sides[s].constant)
                } else if fixed {
                    (64, row_tables[s].0[row] * row_tables[s].1[col] * shift_tables[s][shift])
                } else {
                    (shift, row_tables[s].0[row] * row_tables[s].1[col])
                };
                let weighted = mu[s] * coefficient;
                let slot = &mut acc[s * GROUPS + group];
                let mut m = mask;
                while m != 0 {
                    slot[m.trailing_zeros() as usize] += weighted;
                    m &= m - 1;
                }
            }
            acc
        })
        .reduce(
            || vec![[F128::ZERO; 64]; n_groups],
            |mut x, y| {
                for (a, b) in x.iter_mut().zip(y) {
                    a.iter_mut().zip(b).for_each(|(p, q)| *p += q);
                }
                x
            },
        );
    let mut columns: Vec<Vec<F128>> = sums.into_iter().map(|c| c.to_vec()).collect();
    for side in &sides {
        columns.push(build_eq_table(&side.a));
    }
    for table in &shift_tables {
        for shift in 0..64 {
            columns.push((0..64).map(|t| table[(t + shift) % 64]).collect());
        }
    }
    let target = (0..2).fold(F128::ZERO, |acc, s| acc + mu[s] * (claims.block[s].2 + sides[s].weight * kernel_values[s]));
    let row_term = RowTerm { groups: n_groups };
    let (ops_bits_rounds, tau, finals) = sumcheck::prove(&row_term, columns, target, ch);
    let claim = row_term.eval(&finals);
    let eq_tau = build_eq_table(&tau);
    let mut columns: Vec<Vec<F128>> = vec![
        masks
            .par_iter()
            .map(|&mask| {
                let mut acc = F128::ZERO;
                let mut m = mask;
                while m != 0 {
                    acc += eq_tau[m.trailing_zeros() as usize];
                    m &= m - 1;
                }
                acc
            })
            .collect(),
    ];
    columns.extend(bit_columns(&descriptors, OP_BITS));
    let ops_term = OpsTerm { sides: &sides, mu, tau: &tau };
    let (ops_rounds, ops_point, finals) = sumcheck::prove(&ops_term, columns, claim, ch);
    let (mask, ops) = (finals[0], finals[1..].to_vec());
    ch.observe_f128(mask);
    ch.observe_f128_slice(&ops);
    lap("operations");

    // The Keccak tensor's sumcheck.
    let tensor = &key.bytes[layout.kernel.offset..layout.kernel.offset + (1 << layout.kernel.log)];
    let bits: Vec<F128> = (0..1usize << KERNEL_LOG)
        .into_par_iter()
        .map(|i| if tensor[i >> 3] >> (i & 7) & 1 == 1 { F128::ONE } else { F128::ZERO })
        .collect();
    let half = 1usize << (KERNEL_LOG - 1);
    let mut weights = flock_prover::alloc_zeroed_vec::<F128>(2 * half);
    weights.par_chunks_mut(half).enumerate().for_each(|(s, out)| {
        out.par_chunks_mut(1 << (LOW + WORD_LOG)).enumerate().for_each(|(w, out)| {
            let row = nu[s] * words[s].0[w];
            for (w2, out) in out.chunks_mut(1 << LOW).enumerate() {
                let both = row * words[s].1[w2];
                for (d, slot) in out.iter_mut().enumerate() {
                    *slot = both * pairing[s][d];
                }
            }
        });
    });
    let target = nu[0] * kernel_values[0] + nu[1] * kernel_values[1];
    let (kernel_rounds, kernel_point, finals) = sumcheck::prove(&Product, vec![bits, weights], target, ch);
    let kernel = finals[0];
    ch.observe_f128(kernel);
    lap("Keccak tensor");

    // The live cells' sumcheck.
    let cell_slots = key.slots(layout.cells);
    let cells_term = CellsTerm {
        mu: layout.mu,
        rho: &claims.cells.0,
        c: cc,
    };
    let target = (0..3).fold(F128::ZERO, |acc, i| acc + cc[i] * claims.cells.1[i]);
    let (cells_rounds, cells_point, cells) = sumcheck::prove(&cells_term, bit_columns(&cell_slots, layout.cell_bits()), target, ch);
    ch.observe_f128_slice(&cells);
    lap("cells");

    // The small entries' sumcheck.
    let (small_claims, dense_claims, target) = split_tables(layout, &folded, &coefficients[7..]);
    let small_term = SmallTerm {
        id: layout.small_id,
        index: layout.small_index,
        claims: &small_claims,
    };
    let (small_rounds, small_point, small) =
        sumcheck::prove(&small_term, bit_columns(&key.slots(layout.small), layout.small_bits()), target, ch);
    ch.observe_f128_slice(&small);
    lap("small tables");

    let (bits_nonce, zeta) = ch.grind_pow_and_sample_f128_vec(3, 3 * LOW);
    let mut bit_claims = dense_claims;
    bit_claims.push(list_claim(layout.ops, layout.n, &zeta[..LOW], &ops_point, &ops));
    let local: Vec<F128> = tau.iter().chain(&ops_point).copied().collect();
    bit_claims.push((layout.masks.lift(&local, layout.n), mask));
    bit_claims.push((layout.kernel.lift(&kernel_point, layout.n), kernel));
    bit_claims.push(list_claim(layout.cells, layout.n, &zeta[LOW..2 * LOW], &cells_point, &cells));
    bit_claims.push(list_claim(layout.small, layout.n, &zeta[2 * LOW..], &small_point, &small));
    let all: Vec<Vec<Vec<F128>>> = bit_claims.iter().map(|(p, _)| conjugates(&p[3..])).collect();
    let points: Vec<Vec<F256>> =
        all.iter().flatten().map(|p| p.iter().map(|&c| F256::new(c, F128::ZERO)).collect()).collect();
    let (opened, opening) = whir::open_kept(&key.committed, &points, ch);
    lap("opening");
    let values: Vec<Vec<F128>> = opened
        .chunks(DEGREE)
        .map(|c| {
            c.iter()
                .map(|v| {
                    assert_eq!(v.c1, F128::ZERO, "bytes at a base-field point are in the base field");
                    v.c0
                })
                .collect()
        })
        .collect();
    for ((point, value), ys) in bit_claims.iter().zip(&values) {
        debug_assert_eq!(bit_value(&point[..3], ys), *value, "a bit claim is the committed bytes'");
    }
    return StructProof {
        folds,
        kernel_values,
        batching_nonce,
        ops_bits_rounds,
        ops_rounds,
        mask,
        ops,
        kernel_rounds,
        kernel,
        cells_rounds,
        cells,
        small_rounds,
        small,
        bits_nonce,
        roots: all.into_iter().map(|c| c[1..].to_vec()).collect(),
        values,
        opening,
    };
}

/// Verifies `proof` of `claims` against the commitment of `vk`.
pub fn verify<Ch: Challenger>(vk: &StructVk, claims: &Claims, proof: &StructProof, ch: &mut Ch) -> Result<(), StructError> {
    let layout = &vk.layout;
    if claims.tables.len() != layout.tables.len()
        || proof.folds.len() != layout.tables.len()
        || claims.cells.0.len() != layout.mu
        || proof.ops.len() != OP_BITS
        || proof.cells.len() != layout.cell_bits()
        || proof.small.len() != layout.small_bits()
    {
        return Err(StructError::Shape);
    }
    bind(claims, ch);
    let mut folded = Vec::with_capacity(layout.tables.len());
    for ((&(k, _), groups), folds) in layout.tables.iter().zip(&claims.tables).zip(&proof.folds) {
        let mut out = Vec::with_capacity(2);
        for (group, fold) in groups.iter().zip(folds) {
            if group.is_empty() || group.iter().any(|c| c.row.n_vars() != k || c.col.n_vars() != k) {
                return Err(StructError::Shape);
            }
            out.push(verify_fold_with_grinding(group, fold, FoldGrinding::per_challenge_128(), ch).map_err(|_| StructError::Fold)?);
        }
        let [a, b]: [MatrixClaim; 2] = out.try_into().expect("two sides");
        folded.push([a, b]);
    }
    let side = |s: usize| Side::new(layout, &claims.block[s].0, &claims.block[s].1).ok_or(StructError::Shape);
    let sides = [side(0)?, side(1)?];
    ch.observe_f128_slice(&proof.kernel_values);
    let n_small = small_count(layout);
    let coefficients =
        ch.verify_pow_and_sample_f128_vec(proof.batching_nonce, 1, 7 + n_small).ok_or(StructError::Grinding)?;
    let (mu, nu, cc) = ([coefficients[0], coefficients[1]], [coefficients[2], coefficients[3]], [coefficients[4], coefficients[5], coefficients[6]]);

    let target = (0..2).fold(F128::ZERO, |acc, s| acc + mu[s] * (claims.block[s].2 + sides[s].weight * proof.kernel_values[s]));
    let (claim, tau) = sumcheck::verify(3, LOW, target, &proof.ops_bits_rounds, ch).ok_or(StructError::Grinding)?;
    let ops_term = OpsTerm { sides: &sides, mu, tau: &tau };
    let (claim, ops_point) =
        sumcheck::verify(ops_term.degree(), layout.ops.slots_log(), claim, &proof.ops_rounds, ch).ok_or(StructError::Grinding)?;
    let row: Vec<F128> = std::iter::once(proof.mask).chain(proof.ops.iter().copied()).collect();
    if claim != ops_term.eval(&row) {
        return Err(StructError::Operations);
    }
    ch.observe_f128(proof.mask);
    ch.observe_f128_slice(&proof.ops);

    let target = nu[0] * proof.kernel_values[0] + nu[1] * proof.kernel_values[1];
    let (claim, kernel_point) = sumcheck::verify(2, KERNEL_LOG, target, &proof.kernel_rounds, ch).ok_or(StructError::Grinding)?;
    if claim != proof.kernel * kernel_weight(&sides, nu, &kernel_point) {
        return Err(StructError::Kernel);
    }
    ch.observe_f128(proof.kernel);

    let cells_term = CellsTerm {
        mu: layout.mu,
        rho: &claims.cells.0,
        c: cc,
    };
    let target = (0..3).fold(F128::ZERO, |acc, i| acc + cc[i] * claims.cells.1[i]);
    let (claim, cells_point) =
        sumcheck::verify(cells_term.degree(), layout.cells.slots_log(), target, &proof.cells_rounds, ch).ok_or(StructError::Grinding)?;
    if claim != cells_term.eval(&proof.cells) {
        return Err(StructError::Cells);
    }
    ch.observe_f128_slice(&proof.cells);

    let (small_claims, dense_claims, target) = split_tables(layout, &folded, &coefficients[7..]);
    let small_term = SmallTerm {
        id: layout.small_id,
        index: layout.small_index,
        claims: &small_claims,
    };
    let (claim, small_point) =
        sumcheck::verify(small_term.degree(), layout.small.slots_log(), target, &proof.small_rounds, ch).ok_or(StructError::Grinding)?;
    if claim != small_term.eval(&proof.small) {
        return Err(StructError::Small);
    }
    ch.observe_f128_slice(&proof.small);

    let zeta = ch.verify_pow_and_sample_f128_vec(proof.bits_nonce, 3, 3 * LOW).ok_or(StructError::Grinding)?;
    let mut bit_claims = dense_claims;
    bit_claims.push(list_claim(layout.ops, layout.n, &zeta[..LOW], &ops_point, &proof.ops));
    let local: Vec<F128> = tau.iter().chain(&ops_point).copied().collect();
    bit_claims.push((layout.masks.lift(&local, layout.n), proof.mask));
    bit_claims.push((layout.kernel.lift(&kernel_point, layout.n), proof.kernel));
    bit_claims.push(list_claim(layout.cells, layout.n, &zeta[LOW..2 * LOW], &cells_point, &proof.cells));
    bit_claims.push(list_claim(layout.small, layout.n, &zeta[2 * LOW..], &small_point, &proof.small));
    if proof.roots.len() != bit_claims.len() || proof.values.len() != bit_claims.len() {
        return Err(StructError::Shape);
    }
    let mut points: Vec<Vec<F256>> = Vec::with_capacity(DEGREE * bit_claims.len());
    let mut values: Vec<F256> = Vec::with_capacity(DEGREE * bit_claims.len());
    for (((point, value), roots), ys) in bit_claims.iter().zip(&proof.roots).zip(&proof.values) {
        if roots.len() != DEGREE - 1 || ys.len() != DEGREE {
            return Err(StructError::Shape);
        }
        let mut all = vec![point[3..].to_vec()];
        all.extend(roots.iter().cloned());
        if !are_conjugates(&all) {
            return Err(StructError::Roots);
        }
        if bit_value(&point[..3], ys) != *value {
            return Err(StructError::Bits);
        }
        points.extend(all.iter().map(|p| p.iter().map(|&c| F256::new(c, F128::ZERO)).collect::<Vec<F256>>()));
        values.extend(ys.iter().map(|&y| F256::new(y, F128::ZERO)));
    }
    whir::verify(&vk.config, &vk.commitment, &points, &values, &proof.opening, ch).map_err(|_| StructError::Opening)?;
    return Ok(());
}
