// SPDX-License-Identifier: LGPL-3.0-or-later

//! The fixed tables of a wrapped lift's verifier as one table of bytes, its layout, and its
//! commitment.
//!
//! The bytes hold, each in an aligned region:
//!
//! - every large Boolean table type's two constraint matrices, densely, a bit per entry;
//! - the block's operations, a 64-bit descriptor each, and their row masks, a 64-bit word each;
//! - the shared Keccak-f rows as a dense tensor of bits over side, row word, column word and
//!   offset;
//! - the wrap circuit's live cells with their images under its wiring permutation;
//! - the nonzeros of the small Boolean table types.

use flock_prover::{field::F128, r1cs::SparseBinaryMatrix};
use pofseed_flock_lift_block::{
    committed::Operation,
    kernel::{Kernel, WORD_LOG},
};
use pofseed_flock_lift_whir::{
    params::{Config, MerkleHash, Regime},
    whir::{self, Commitment, Committed},
};
use rayon::prelude::*;

use crate::subfield::embed;

/// Bits of a block word index in a descriptor.
pub const WORD_BITS: usize = 22;

/// Bits of an operation descriptor: the Keccak flag, the side, the fixed flag, the shift, and the
/// row and column words.
pub const OP_BITS: usize = 3 + 6 + 2 * WORD_BITS;

/// log2 of the bits of the Keccak tensor: the offset, two local words and the side.
pub const KERNEL_LOG: usize = 6 + 2 * WORD_LOG + 1;

/// The two constraint matrices of a Boolean table type.
#[derive(Clone)]
pub struct Table {
    /// log2 of the type's rows and columns.
    pub k_log: usize,
    /// The `A` matrix.
    pub a: SparseBinaryMatrix,
    /// The `B` matrix.
    pub b: SparseBinaryMatrix,
}

/// What the fixed tables are built from.
pub struct Parts {
    /// log2 of the block's width in bits.
    pub k_log: usize,
    /// The block's sub-blocks before the first Keccak-f one.
    pub head_subs: usize,
    /// The block's Keccak-f sub-blocks.
    pub keccak_subs: usize,
    /// The block's operations.
    pub operations: Vec<Operation>,
    /// The distinct Boolean table types' matrices.
    pub tables: Vec<Table>,
    /// log2 of the wrap circuit's rows.
    pub nu: usize,
    /// log2 of the wrap circuit's cells.
    pub mu: usize,
    /// Live rows of every cell slot.
    pub live: Vec<usize>,
    /// The wiring permutation over the cells.
    pub sigma: Vec<usize>,
}

/// An aligned region of the bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    /// The region's first byte.
    pub offset: usize,
    /// log2 of the region's bytes.
    pub log: usize,
}

/// How a table type's matrices are held.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Held {
    /// Densely, in two regions, `A` then `B`.
    Dense([Region; 2]),
    /// As entries of the small list, under the given identifier for `A` and the next for `B`.
    Small(usize),
}

/// Where everything sits in the bytes, and the widths of the lists' fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// log2 of the bytes.
    pub n: usize,
    /// log2 of the block's width in bits.
    pub k_log: usize,
    /// The block's sub-blocks before the first Keccak-f one.
    pub head_subs: usize,
    /// The block's Keccak-f sub-blocks.
    pub keccak_subs: usize,
    /// Per table, its log size and how it is held.
    pub tables: Vec<(usize, Held)>,
    /// The operation descriptors, 8 bytes each.
    pub ops: Region,
    /// The operations' masks, 8 bytes each, in the descriptors' order.
    pub masks: Region,
    /// The Keccak tensor.
    pub kernel: Region,
    /// The live cells, 8 bytes each.
    pub cells: Region,
    /// log2 of the wrap circuit's cells.
    pub mu: usize,
    /// The small tables' entries, 8 bytes each.
    pub small: Region,
    /// Bits of a small entry's identifier.
    pub small_id: usize,
    /// Bits of a small entry's row and of its column.
    pub small_index: usize,
}

impl Region {
    /// log2 of the 64-bit slots in the region.
    pub fn slots_log(&self) -> usize {
        return self.log - 3;
    }

    /// The point over the bytes' bits at which the region's local point `local` sits.
    pub fn lift(&self, local: &[F128], n: usize) -> Vec<F128> {
        assert_eq!(local.len(), 3 + self.log);
        let mut point = local.to_vec();
        let prefix = self.offset >> self.log;
        point.extend((0..n - self.log).map(|i| if prefix >> i & 1 == 1 { F128::ONE } else { F128::ZERO }));
        return point;
    }
}

fn ceil_log(n: usize) -> usize {
    return n.max(1).next_power_of_two().trailing_zeros() as usize;
}

fn nnz(m: &SparseBinaryMatrix) -> usize {
    return m.rows.iter().map(Vec::len).sum();
}

/// A descriptor of an operation.
pub fn pack_op(op: &Operation) -> u64 {
    return (op.side as u64) << 1 | (op.fixed as u64) << 2 | (op.shift as u64) << 3 | (op.row_word as u64) << 9 | (op.col_word as u64) << (9 + WORD_BITS);
}

/// A descriptor of the constant-wire read of a Keccak row word on a side.
pub fn pack_constant(side: u8, word: u16) -> u64 {
    return 1 | (side as u64) << 1 | (word as u64) << 9;
}

/// The descriptors and masks of a block's operations followed by its Keccak rows' constant reads.
pub fn descriptors(operations: &[Operation], kernel: &Kernel) -> Vec<(u64, u64)> {
    let mut out: Vec<(u64, u64)> = operations.iter().map(|op| (pack_op(op), op.mask)).collect();
    out.extend(kernel.constant.iter().map(|&(side, word, mask)| (pack_constant(side, word), mask)));
    return out;
}

/// The live cells and their images, as list entries.
fn cells(parts: &Parts) -> Vec<u64> {
    assert!(2 * parts.mu < 64, "a cell and its image fit an entry");
    let rows = 1usize << parts.nu;
    let mut out = Vec::new();
    for (slot, &count) in parts.live.iter().enumerate() {
        for row in 0..count.min(rows) {
            let x = slot << parts.nu | row;
            out.push(1 | (x as u64) << 1 | (parts.sigma[x] as u64) << (1 + parts.mu));
        }
    }
    return out;
}

impl Layout {
    fn new(parts: &Parts, kernel: &Kernel) -> (Layout, Vec<u64>, Vec<u64>) {
        assert!(parts.k_log <= WORD_BITS + 6, "the descriptors hold blocks of at most 2^28 bits");
        let cell_list = cells(parts);
        let dense: Vec<bool> =
            parts.tables.iter().map(|t| 64 * (nnz(&t.a) + nnz(&t.b)) > 2 << (2 * t.k_log)).collect();
        let small_tables: Vec<usize> = (0..parts.tables.len()).filter(|&i| !dense[i]).collect();
        let small_index = small_tables.iter().map(|&i| parts.tables[i].k_log).max().unwrap_or(1);
        let small_id = ceil_log(2 * small_tables.len()).max(1);
        assert!(1 + small_id + 2 * small_index <= 64, "a small entry fits 64 bits");
        let mut small_list: Vec<u64> = Vec::new();
        for (id, &i) in small_tables.iter().enumerate() {
            for (side, m) in [&parts.tables[i].a, &parts.tables[i].b].into_iter().enumerate() {
                for (r, row) in m.rows.iter().enumerate() {
                    for &c in row {
                        small_list.push(
                            1 | ((2 * id + side) as u64) << 1 | (r as u64) << (1 + small_id) | (c as u64) << (1 + small_id + small_index),
                        );
                    }
                }
            }
        }
        let ops_log = 3 + ceil_log(parts.operations.len() + kernel.constant.len());
        // Regions by decreasing size, so that the running offset stays aligned.
        let mut sizes: Vec<(usize, usize)> = Vec::new();
        let dense_at: Vec<Option<usize>> = (0..parts.tables.len())
            .map(|i| {
                dense[i].then(|| {
                    sizes.push((2 * parts.tables[i].k_log - 3, sizes.len()));
                    sizes.push((2 * parts.tables[i].k_log - 3, sizes.len()));
                    sizes.len() - 2
                })
            })
            .collect();
        let fixed = sizes.len();
        for log in [ops_log, ops_log, KERNEL_LOG - 3, 3 + ceil_log(cell_list.len()), 3 + ceil_log(small_list.len())] {
            sizes.push((log, sizes.len()));
        }
        let mut order = sizes.clone();
        order.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        let mut regions = vec![Region { offset: 0, log: 0 }; sizes.len()];
        let mut offset = 0usize;
        for (log, index) in order {
            regions[index] = Region { offset, log };
            offset += 1 << log;
        }
        let mut small_ids = 0;
        let tables = (0..parts.tables.len())
            .map(|i| {
                let held = match dense_at[i] {
                    Some(at) => Held::Dense([regions[at], regions[at + 1]]),
                    None => {
                        small_ids += 2;
                        Held::Small(small_ids - 2)
                    }
                };
                (parts.tables[i].k_log, held)
            })
            .collect();
        let layout = Layout {
            n: ceil_log(offset),
            k_log: parts.k_log,
            head_subs: parts.head_subs,
            keccak_subs: parts.keccak_subs,
            tables,
            ops: regions[fixed],
            masks: regions[fixed + 1],
            kernel: regions[fixed + 2],
            cells: regions[fixed + 3],
            mu: parts.mu,
            small: regions[fixed + 4],
            small_id,
            small_index,
        };
        return (layout, cell_list, small_list);
    }

    /// Bits of a cell entry: the live flag, the cell and its image.
    pub fn cell_bits(&self) -> usize {
        return 1 + 2 * self.mu;
    }

    /// Bits of a small entry: the valid flag, the identifier, the row and the column.
    pub fn small_bits(&self) -> usize {
        return 1 + self.small_id + 2 * self.small_index;
    }
}

fn write_slots(bytes: &mut [u8], region: Region, slots: &[u64]) {
    assert!(slots.len() <= 1 << region.slots_log());
    for (k, &slot) in slots.iter().enumerate() {
        bytes[region.offset + 8 * k..region.offset + 8 * k + 8].copy_from_slice(&slot.to_le_bytes());
    }
}

/// What proving evaluations of the fixed tables needs.
pub struct StructKey {
    /// The layout.
    pub layout: Layout,
    /// The bytes.
    pub bytes: Vec<u8>,
    /// The commitment's parameters.
    pub config: Config,
    /// The commitment and what opening it needs.
    pub committed: Committed,
    /// The commitment.
    pub commitment: Commitment,
    /// The tables' matrices.
    pub tables: Vec<Table>,
    /// The Keccak rows at the level of lanes.
    pub kernel: Kernel,
}

/// What verifying evaluations of the fixed tables needs.
#[derive(Clone, Debug, PartialEq)]
pub struct StructVk {
    /// The layout.
    pub layout: Layout,
    /// The commitment's parameters.
    pub config: Config,
    /// The commitment.
    pub commitment: Commitment,
}

/// The commitment parameters for bytes of `2^n`, at rate `2^-log_inv_rate`.
pub fn config(n: usize, log_inv_rate: usize) -> Config {
    return Config {
        num_vars: n,
        folding: 4,
        log_inv_rate,
        security_bits: 128,
        pow_bits: 22,
        final_vars: 3.min(n - 1),
        regime: Regime::Johnson,
        merkle: MerkleHash::Keccak,
    };
}

impl StructKey {
    /// Lays the tables of `parts` out and commits to them at rate `2^-log_inv_rate`.
    pub fn new(parts: Parts, log_inv_rate: usize) -> Self {
        let kernel = Kernel::new();
        let (layout, cell_list, small_list) = Layout::new(&parts, &kernel);
        let mut bytes = vec![0u8; 1 << layout.n];
        for (table, &(k, held)) in parts.tables.iter().zip(&layout.tables) {
            if let Held::Dense(regions) = held {
                for (m, region) in [&table.a, &table.b].into_iter().zip(regions) {
                    for (r, row) in m.rows.iter().enumerate() {
                        for &c in row {
                            let bit = c + (r << k);
                            bytes[region.offset + (bit >> 3)] |= 1 << (bit & 7);
                        }
                    }
                }
            }
        }
        let (descriptors, masks): (Vec<u64>, Vec<u64>) = descriptors(&parts.operations, &kernel).into_iter().unzip();
        write_slots(&mut bytes, layout.ops, &descriptors);
        write_slots(&mut bytes, layout.masks, &masks);
        for &(side, w, w2, mask) in &kernel.words {
            let slot = (side as usize) << (2 * WORD_LOG) | (w as usize) << WORD_LOG | w2 as usize;
            bytes[layout.kernel.offset + 8 * slot..layout.kernel.offset + 8 * slot + 8].copy_from_slice(&mask.to_le_bytes());
        }
        write_slots(&mut bytes, layout.cells, &cell_list);
        write_slots(&mut bytes, layout.small, &small_list);
        let config = config(layout.n, log_inv_rate);
        let message: Vec<F128> = bytes.par_iter().map(|&b| embed(b)).collect();
        let (commitment, committed) = whir::commit(&config, message).expect("secure parameters");
        return Self {
            layout,
            bytes,
            config,
            committed,
            commitment,
            tables: parts.tables,
            kernel,
        };
    }

    /// What verifying needs.
    pub fn verifying(&self) -> StructVk {
        return StructVk {
            layout: self.layout.clone(),
            config: self.config,
            commitment: self.commitment.clone(),
        };
    }

    /// The 64-bit slots of a region.
    pub fn slots(&self, region: Region) -> Vec<u64> {
        return self.bytes[region.offset..region.offset + (1 << region.log)]
            .chunks(8)
            .map(|c| u64::from_le_bytes(c.try_into().expect("eight bytes")))
            .collect();
    }
}
