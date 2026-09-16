// SPDX-License-Identifier: LGPL-3.0-or-later

//! Measures how far the discharge stream's explicit rows collapse into classes that a contract
//! could sum in closed form: rows of one output word whose operands, taken relative to the
//! output bit modulo 64, are the same.

use std::collections::HashMap;

use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::stream::{ROW, records};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1};
use pofseed_flock_lift_statement::HardenedChildCircuit;

/// Columns below this are fixed wires (the constant, challenge bits and published words).
const FIXED: u32 = 32 * 128;

/// An operand relative to the output bit: a fixed column, or a word and a cyclic bit offset.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Operand {
    Fixed(u32),
    Rel(u32, u8),
}

/// An operand relative to the output word as well.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Shape {
    Fixed(u32),
    Rel(i64, u8),
}

fn relative(cols: &[u32], t: u32) -> Vec<Operand> {
    let mut v: Vec<Operand> = cols
        .iter()
        .map(|&c| if c < FIXED { Operand::Fixed(c) } else { Operand::Rel(c >> 6, ((c & 63) + 64 - t) as u8 % 64) })
        .collect();
    v.sort_unstable();
    return v;
}

fn shape(ops: &[Operand], word: u32) -> Vec<Shape> {
    return ops
        .iter()
        .map(|o| match *o {
            Operand::Fixed(c) => Shape::Fixed(c),
            Operand::Rel(w, s) => Shape::Rel(w as i64 - word as i64, s),
        })
        .collect();
}

fn contiguous(mask: u64) -> bool {
    let m = mask >> mask.trailing_zeros();
    return m & (m.wrapping_add(1)) == 0;
}

fn main() {
    let (_, chain_code) = bip32_vector_1();
    let program = Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET));
    let recs = records(&program);
    let mut classes: HashMap<(u32, Vec<Operand>, Vec<Operand>), u64> = HashMap::new();
    let mut rows = 0usize;
    let mut refs = 0usize;
    for r in recs.iter().filter(|r| r[0] == ROW) {
        let col = u32::from_be_bytes(r[1..5].try_into().unwrap());
        let na = u16::from_be_bytes(r[5..7].try_into().unwrap()) as usize;
        let nb = u16::from_be_bytes(r[7..9].try_into().unwrap()) as usize;
        let cols: Vec<u32> = r[9..].chunks(4).map(|c| u32::from_be_bytes(c.try_into().unwrap())).collect();
        assert_eq!(cols.len(), na + nb);
        let t = col & 63;
        if std::env::var("CLASS_WORD").ok().and_then(|w| w.parse::<u32>().ok()) == Some(col >> 6) {
            let fmt = |v: &[u32]| v.iter().map(|&c| if c < FIXED { format!("#{c}") } else { format!("{}.{}", c >> 6, c & 63) }).collect::<Vec<_>>().join(" ");
            println!("bit {t}: A [{}] B [{}]", fmt(&cols[..na]), fmt(&cols[na..]));
        }
        let key = (col >> 6, relative(&cols[..na], t), relative(&cols[na..], t));
        let mask = classes.entry(key).or_insert(0);
        assert_eq!(*mask & (1 << t), 0, "a row repeats in its class");
        *mask |= 1 << t;
        rows += 1;
        refs += na + nb;
    }
    if std::env::var_os("CLASS_WORD").is_some() {
        return;
    }
    let mut heavy: Vec<(usize, u32)> = Vec::new();
    for (word, a, b) in classes.keys() {
        heavy.push((a.len() + b.len(), *word));
    }
    heavy.sort_unstable();
    println!("heaviest rows' words: {:?}", &heavy[heavy.len() - 5..]);
    println!("median operands per row: {}", heavy[heavy.len() / 2].0);
    let mut class_refs = 0usize;
    let mut ranges = 0usize;
    let mut range_refs = 0usize;
    let mut by_size = [0usize; 65];
    let mut shapes: HashMap<(Vec<Shape>, Vec<Shape>, u64), usize> = HashMap::new();
    for ((word, a, b), mask) in &classes {
        let ops = a.len() + b.len();
        class_refs += ops;
        by_size[mask.count_ones() as usize] += mask.count_ones() as usize;
        let mut m = *mask;
        while m != 0 {
            let lo = m.trailing_zeros();
            let run = (!(m >> lo)).trailing_zeros();
            ranges += 1;
            range_refs += ops;
            m &= !(if run == 64 { u64::MAX } else { ((1u64 << run) - 1) << lo });
        }
        let _ = contiguous(*mask);
        *shapes.entry((shape(a, *word), shape(b, *word), *mask)).or_insert(0) += 1;
    }
    println!("stream rows {rows}, column references {refs}");
    println!("classes (same output word, same operands modulo a cyclic bit shift): {}, carrying {class_refs} operands", classes.len());
    println!("  as contiguous bit ranges: {ranges} ranges, carrying {range_refs} operands");
    println!("rows by class size:");
    for (k, n) in by_size.iter().enumerate().filter(|&(_, &n)| n > 0) {
        println!("  {k:>2} bits: {n} rows");
    }
    let shape_refs: usize = shapes.keys().map(|(a, b, _)| a.len() + b.len()).sum();
    println!(
        "shapes (classes equal up to their output word, with the same bit mask): {}, carrying {shape_refs} operands",
        shapes.len()
    );
    let mut counts: Vec<usize> = shapes.values().copied().collect();
    counts.sort_unstable_by(|x, y| y.cmp(x));
    let top: usize = counts.iter().take(100).sum();
    println!("  the 100 most repeated shapes cover {top} classes of {}", classes.len());
}
