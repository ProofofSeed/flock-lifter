// SPDX-License-Identifier: LGPL-3.0-or-later

//! The explicit rows of a block as a public list of entries whose table-weighted sum is the rows'
//! share of a lincheck matrix claim.
//!
//! A row's weight is `skip[t]·eq(x, W)` for its column `W·64 + t`, and an operand's is
//! `z[t']·eq(r, W')` for its column `W'·64 + t'`. Rows of one output word whose operands keep a
//! fixed word and a fixed cyclic bit offset — or a fixed column, for the columns below
//! [`ABSOLUTE_BELOW`] — form a class, and a class contributes, per operand and per contiguous run
//! `[a, b)` of its row bits,
//!
//! `side · eq(x, W) · eq(r, W') · (P[u][b] + P[u][a])`,
//!
//! where `P[u][j] = Σ_{t<j} skip[t]·Z_u[t]` with `Z_u[t] = z[(t + u) mod 64]` for an offset
//! `u < 64` and `Z_u[t] = z[u − 64]` for a fixed column bit `u − 64`. Each of those two terms is an
//! entry. Entries that occur an even number of times cancel and are dropped.

use std::collections::HashMap;

use flock_prover::{field::F128, lincheck::build_eq_table};
use rayon::prelude::*;

use crate::program::Program;

/// Columns below this keep their bit across a class's rows; the rest shift with the row bit.
pub const ABSOLUTE_BELOW: u32 = 64 * 64;

/// Rows of the prefix table: 64 cyclic offsets, then 64 fixed column bits.
pub const P_ROWS: usize = 128;

/// Columns of the prefix table: run ends `0..=64`.
pub const P_COLS: usize = 65;

/// Address stride of the prefix table: an address is `u·P_STRIDE + j`, so that its bits split
/// into those of `u` and those of `j`.
pub const P_STRIDE: usize = 128;

/// Bits of the prefix-table address.
pub const P_BITS: usize = 14;

/// Bit widths of the lookups an entry makes, in order: side, three row-word chunks, three
/// column-word chunks, prefix table.
pub const LOOKUP_BITS: [usize; 8] = [1, 8, 8, 6, 8, 8, 6, P_BITS];

/// Word bits of the largest block the packing holds, `2^28` bits; a smaller block's points are
/// padded with zeros.
pub const WORD_BITS: usize = 22;

/// An entry, packed: bit 0 the side (0 for A, 1 for B), bits 1..23 the row word, bits 23..45 the
/// column word, bits 45..59 the prefix-table address `u·128 + j`.
pub type Entry = u64;

/// Packs an entry.
pub fn pack(side: usize, row_word: u32, col_word: u32, u: usize, j: usize) -> Entry {
    debug_assert!(side < 2 && u < P_ROWS && j < P_COLS);
    debug_assert!(row_word >> WORD_BITS == 0 && col_word >> WORD_BITS == 0);
    return side as u64 | (row_word as u64) << 1 | (col_word as u64) << 23 | ((u * P_STRIDE + j) as u64) << 45;
}

/// The address an entry reads in lookup `l`.
pub fn address(entry: Entry, l: usize) -> usize {
    let row = (entry >> 1) & ((1 << WORD_BITS) - 1);
    let col = (entry >> 23) & ((1 << WORD_BITS) - 1);
    return match l {
        0 => (entry & 1) as usize,
        1 => (row & 0xff) as usize,
        2 => ((row >> 8) & 0xff) as usize,
        3 => (row >> 16) as usize,
        4 => (col & 0xff) as usize,
        5 => ((col >> 8) & 0xff) as usize,
        6 => (col >> 16) as usize,
        7 => (entry >> 45) as usize,
        _ => unreachable!("an entry makes eight lookups"),
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Operand {
    Absolute(u8, u32),
    Relative(u8, u32, u8),
}

/// One operand of one class of explicit rows: the rows `W·64 + t` for the bits `t` of `mask` read,
/// on side `side`, the column `col_word·64 + (t + shift) mod 64`, or the column
/// `col_word·64 + shift` at every row when `fixed`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Operation {
    /// 0 for `A`, 1 for `B`.
    pub side: u8,
    /// Whether the column keeps its bit across the rows.
    pub fixed: bool,
    /// The cyclic bit offset, or the fixed column bit.
    pub shift: u8,
    /// The rows' word.
    pub row_word: u32,
    /// The column's word.
    pub col_word: u32,
    /// The rows' bits.
    pub mask: u64,
}

fn classes(program: &Program) -> HashMap<(u32, Vec<Operand>), u64> {
    assert!(program.geometry().k_log() <= WORD_BITS + 6, "the entry packing holds blocks of at most 2^28 bits");
    let mut classes: HashMap<(u32, Vec<Operand>), u64> = HashMap::new();
    for r in 0..program.explicit_rows() {
        let (col, a, b) = program.explicit_row(r);
        let t = col & 63;
        let mut ops: Vec<Operand> = Vec::with_capacity(a.len() + b.len());
        for (side, cols) in [a, b].into_iter().enumerate() {
            for &c in cols {
                ops.push(if c < ABSOLUTE_BELOW {
                    Operand::Absolute(side as u8, c)
                } else {
                    Operand::Relative(side as u8, c >> 6, (((c & 63) + 64 - t) % 64) as u8)
                });
            }
        }
        ops.sort_unstable();
        let mask = classes.entry((col >> 6, ops)).or_insert(0);
        assert_eq!(*mask >> t & 1, 0, "row {r} repeats in its class");
        *mask |= 1 << t;
    }
    return classes;
}

/// The operations of `program`'s explicit rows, sorted, with those that cancel merged: operations
/// agreeing in everything but their rows are one operation over the rows an odd number of them cover.
pub fn operations(program: &Program) -> Vec<Operation> {
    let mut merged: HashMap<(u8, bool, u8, u32, u32), u64> = HashMap::new();
    for ((row_word, ops), mask) in classes(program) {
        for op in ops {
            let key = match op {
                Operand::Absolute(side, c) => (side, true, (c & 63) as u8, row_word, c >> 6),
                Operand::Relative(side, w, s) => (side, false, s, row_word, w),
            };
            *merged.entry(key).or_insert(0) ^= mask;
        }
    }
    let mut out: Vec<Operation> = merged
        .into_iter()
        .filter(|&(_, mask)| mask != 0)
        .map(|((side, fixed, shift, row_word, col_word), mask)| Operation {
            side,
            fixed,
            shift,
            row_word,
            col_word,
            mask,
        })
        .collect();
    out.par_sort_unstable();
    return out;
}

/// The entries of `program`'s explicit rows, sorted, with pairs cancelled.
pub fn entries(program: &Program) -> Vec<Entry> {
    let classes = classes(program);
    let mut out: Vec<Entry> = classes
        .into_par_iter()
        .flat_map_iter(|((row_word, ops), mask)| {
            let mut runs = Vec::new();
            let mut m = mask;
            while m != 0 {
                let a = m.trailing_zeros() as usize;
                let len = (!(m >> a)).trailing_zeros() as usize;
                runs.push((a, a + len));
                m &= if a + len == 64 { !(u64::MAX << a) } else { !(((1u64 << len) - 1) << a) };
            }
            let mut v = Vec::with_capacity(2 * runs.len() * ops.len());
            for op in ops {
                let (side, col_word, u) = match op {
                    Operand::Absolute(side, c) => (side, c >> 6, 64 + (c & 63) as usize),
                    Operand::Relative(side, w, s) => (side, w, s as usize),
                };
                for &(a, b) in &runs {
                    v.push(pack(side as usize, row_word, col_word, u, b));
                    if a > 0 {
                        v.push(pack(side as usize, row_word, col_word, u, a));
                    }
                }
            }
            v
        })
        .collect();
    out.par_sort_unstable();
    let mut kept = Vec::with_capacity(out.len());
    let mut i = 0;
    while i < out.len() {
        let mut j = i;
        while j < out.len() && out[j] == out[i] {
            j += 1;
        }
        if (j - i) % 2 == 1 {
            kept.push(out[i]);
        }
        i = j;
    }
    return kept;
}

/// The tables a claim reads the entries through.
pub struct Tables {
    /// One table per lookup, in [`LOOKUP_BITS`] order.
    pub tables: [Vec<F128>; 8],
}

impl Tables {
    /// The tables of the claim with A-side challenge `alpha`, row skip weights `skip`, collapsed
    /// witness `z`, row point `x` and column point `r`, the points LSB-first and at most
    /// [`WORD_BITS`] long.
    pub fn new(alpha: F128, skip: &[F128], z: &[F128], x: &[F128], r: &[F128]) -> Self {
        assert!(skip.len() == 64 && z.len() == 64 && x.len() <= WORD_BITS && r.len() == x.len());
        let pad = |v: &[F128]| -> Vec<F128> {
            let mut v = v.to_vec();
            v.resize(WORD_BITS, F128::ZERO);
            v
        };
        let (x, r) = (pad(x), pad(r));
        let mut p = vec![F128::ZERO; 1 << P_BITS];
        for u in 0..P_ROWS {
            let mut acc = F128::ZERO;
            for j in 0..P_COLS {
                p[u * P_STRIDE + j] = acc;
                if j < 64 {
                    let zt = if u < 64 { z[(j + u) % 64] } else { z[u - 64] };
                    acc += skip[j] * zt;
                }
            }
        }
        return Self {
            tables: [
                vec![alpha, F128::ONE],
                build_eq_table(&x[..8]),
                build_eq_table(&x[8..16]),
                build_eq_table(&x[16..]),
                build_eq_table(&r[..8]),
                build_eq_table(&r[8..16]),
                build_eq_table(&r[16..]),
                p,
            ],
        };
    }

    /// The product of the values `entry` reads.
    pub fn term(&self, entry: Entry) -> F128 {
        let mut acc = F128::ONE;
        for (l, t) in self.tables.iter().enumerate() {
            acc *= t[address(entry, l)];
        }
        return acc;
    }
}

/// The table-weighted sum of `entries`.
pub fn value(entries: &[Entry], tables: &Tables) -> F128 {
    return entries.par_iter().map(|&e| tables.term(e)).reduce(|| F128::ZERO, |a, b| a + b);
}
