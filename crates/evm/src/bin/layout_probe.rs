// SPDX-License-Identifier: LGPL-3.0-or-later

//! Estimates what the replay rows would cost a contract if the compiler laid every gate's
//! columns out bit-aligned, one 64-bit word per gate and column kind: the replay rows are
//! remapped onto that virtual layout and grouped into classes a contract could sum in closed
//! form, rows of one output word whose operands keep a fixed word and cyclic bit offset.

use std::collections::{BTreeSet, HashMap};

use pofseed_flock_lift_block::{form::CONST, program::Program, replay};
use pofseed_flock_lift_evm::stream::{ROW, records};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1};
use pofseed_flock_lift_statement::HardenedChildCircuit;

/// Columns below this are the constant, the challenge bits and other fixed wires.
const FIXED: u64 = 32 * 128;

/// Column kinds per gate in the virtual layout.
const KINDS: u64 = 6;

/// Limbs per gate and column kind in the virtual layout.
const LIMBS: u64 = 64;

/// Gas per field multiplication, per table lookup and per class, for the cost model.
const MUL_GAS: u64 = 1_800;
const LOOKUP_GAS: u64 = 150;
const CLASS_GAS: u64 = 2_000;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Operand {
    Fixed(u64),
    Rel(u64, u8),
}

#[derive(Default)]
struct Class {
    mask: u64,
    const_a: u64,
    const_b: u64,
}

fn contiguous(mask: u64) -> bool {
    let m = mask >> mask.trailing_zeros();
    return m & m.wrapping_add(1) == 0;
}

fn relative(cols: impl Iterator<Item = u64>, t: u64) -> (Vec<Operand>, bool) {
    let mut konst = false;
    let mut v = Vec::new();
    for c in cols {
        if c == CONST as u64 {
            konst = true;
        } else if c < FIXED {
            v.push(Operand::Fixed(c));
        } else {
            v.push(Operand::Rel(c >> 6, ((c & 63) + 64 - t) as u8 % 64));
        }
    }
    v.sort_unstable();
    return (v, konst);
}

fn side_muls(ops: &[Operand]) -> usize {
    let shifts: BTreeSet<u8> = ops
        .iter()
        .filter_map(|o| if let Operand::Rel(_, s) = o { Some(*s) } else { None })
        .collect();
    let fixed = ops.iter().any(|o| matches!(o, Operand::Fixed(_)));
    return shifts.len() + fixed as usize;
}

fn analyse(name: &str, rows: &[(u64, Vec<u64>, Vec<u64>)]) {
    let mut classes: HashMap<(u64, Vec<Operand>, Vec<Operand>), Class> = HashMap::new();
    let mut refs = 0usize;
    for (col, a, b) in rows {
        let t = col & 63;
        let (ra, ka) = relative(a.iter().copied(), t);
        let (rb, kb) = relative(b.iter().copied(), t);
        refs += a.len() + b.len();
        let class = classes.entry((col >> 6, ra, rb)).or_default();
        assert_eq!(class.mask & (1 << t), 0, "a row repeats in its class");
        class.mask |= 1 << t;
        class.const_a |= (ka as u64) << t;
        class.const_b |= (kb as u64) << t;
    }
    let mut operands = 0usize;
    let mut gas = 0u64;
    let mut rows_in_big = 0usize;
    let mut by_size = [0usize; 65];
    let (mut full, mut ranged, mut scattered) = (0usize, 0usize, 0usize);
    let (mut total_muls, mut total_lookups) = (0usize, 0usize);
    for ((_, a, b), class) in &classes {
        let bits = class.mask.count_ones() as usize;
        by_size[bits] += bits;
        if bits >= 8 {
            rows_in_big += bits;
        }
        operands += a.len() + b.len();
        let masked = |m: u64| if m == 0 { 0 } else { 1 };
        let muls = side_muls(a) + side_muls(b) + masked(class.const_a) + masked(class.const_b) + 1;
        let per_sum = if class.mask == u64::MAX {
            full += 1;
            1
        } else if contiguous(class.mask) {
            ranged += 1;
            2
        } else {
            scattered += 1;
            8
        };
        let lookups = a.len() + b.len() + 8 * (masked(class.const_a) + masked(class.const_b)) + per_sum * muls;
        gas += CLASS_GAS + MUL_GAS * muls as u64 + LOOKUP_GAS * lookups as u64;
        total_muls += muls;
        total_lookups += lookups;
    }
    println!("{name}:");
    println!("  rows {}, column references {refs}", rows.len());
    println!("  classes {}, carrying {operands} operands; {rows_in_big} rows in classes of 8 bits or more", classes.len());
    println!(
        "  bit counts of classes (rows): 1: {}, 2-7: {}, 8-63: {}, 64: {}",
        by_size[1],
        by_size[2..8].iter().sum::<usize>(),
        by_size[8..64].iter().sum::<usize>(),
        by_size[64]
    );
    println!("  classes over a whole word {full}, over a contiguous bit range {ranged}, over other bit sets {scattered}");
    println!("  modelled work per claim: {total_muls} multiplications, {total_lookups} lookups, {} classes", classes.len());
    println!("  modelled closed-form gas per claim: {:.1} M", gas as f64 / 1e6);
}

fn main() {
    let (_, chain_code) = bip32_vector_1();
    let circuit = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let program = Program::new(&circuit);
    let geometry = program.geometry().clone();
    let replay = replay::compile(&circuit, &geometry).expect("the replay fits");
    let base = geometry.replay_base() as u64;
    let end = replay.end_col as u64;
    let gates = replay.origins.iter().map(|o| o.0).max().unwrap_or(0) as u64 + 1;
    println!(
        "replay: {} rows, columns {base}..{end}, {gates} column-allocating gates, {} products, {} materialised",
        replay.rows.len(),
        replay.products,
        replay.materialised
    );
    let vbase = 1u64 << 40;
    let remap = |c: u32| -> u64 {
        let c = c as u64;
        if c >= base && c < end {
            let (g, k, b) = replay.origins[(c - base) as usize];
            return vbase + ((((g as u64 * KINDS + k as u64) * LIMBS) + (b as u64 >> 6)) << 6) + (b as u64 & 63);
        }
        return c;
    };
    let actual: Vec<(u64, Vec<u64>, Vec<u64>)> = replay
        .rows
        .iter()
        .map(|r| {
            (
                r.col as u64,
                r.a.cols().iter().map(|&c| c as u64).collect(),
                r.b.cols().iter().map(|&c| c as u64).collect(),
            )
        })
        .collect();
    let virtual_rows: Vec<(u64, Vec<u64>, Vec<u64>)> = replay
        .rows
        .iter()
        .map(|r| (remap(r.col), r.a.cols().iter().map(|&c| remap(c)).collect(), r.b.cols().iter().map(|&c| remap(c)).collect()))
        .collect();
    if let Ok(g) = std::env::var("PROBE_GATE") {
        let g: u64 = g.parse().expect("gate");
        let show = |c: u64| -> String {
            if c >= vbase {
                let v = c - vbase;
                format!("g{}k{}l{}.{}", (v >> 6) / LIMBS / KINDS, (v >> 6) / LIMBS % KINDS, (v >> 6) % LIMBS, v & 63)
            } else {
                format!("{}.{}", c >> 6, c & 63)
            }
        };
        for (col, a, b) in &virtual_rows {
            if *col >= vbase && ((col - vbase) >> 6) / LIMBS / KINDS == g && (col & 63) < 6 {
                let fa: Vec<String> = a.iter().map(|&c| show(c)).collect();
                let fb: Vec<String> = b.iter().map(|&c| show(c)).collect();
                println!("{} A [{}] B [{}]", show(*col), fa.join(" "), fb.join(" "));
            }
        }
        return;
    }
    analyse("replay rows as compiled", &actual);
    analyse("replay rows, bit-aligned per gate and column kind", &virtual_rows);
    report_words("virtual layout", &replay.origins);
    let uniform = replay::compile_uniform(&circuit, &geometry);
    let ubase = base;
    let uend = uniform.end_col as u64;
    println!(
        "uniform replay: {} rows, {} columns, {} products, {} materialised",
        uniform.rows.len(),
        uend - ubase,
        uniform.products,
        uniform.materialised
    );
    let uremap = |c: u32| -> u64 {
        let c = c as u64;
        if c >= ubase && c < uend {
            let (g, k, b) = uniform.origins[(c - ubase) as usize];
            return vbase + ((((g as u64 * KINDS + k as u64) * LIMBS) + (b as u64 >> 6)) << 6) + (b as u64 & 63);
        }
        return c;
    };
    let urows: Vec<(u64, Vec<u64>, Vec<u64>)> = uniform
        .rows
        .iter()
        .map(|r| (uremap(r.col), r.a.cols().iter().map(|&c| uremap(c)).collect(), r.b.cols().iter().map(|&c| uremap(c)).collect()))
        .collect();
    analyse("uniform replay rows, bit-aligned per gate and column kind", &urows);
    report_words("uniform layout", &uniform.origins);
    let program = Program::uniform(&circuit);
    let geometry = program.geometry().clone();
    let replay = replay::compile_uniform(&circuit, &geometry);
    let base = geometry.replay_base() as u64;
    let end = replay.end_col as u64;
    let remap = |c: u32| -> u64 {
        let c = c as u64;
        if c >= base && c < end {
            let (g, k, b) = replay.origins[(c - base) as usize];
            return vbase + ((((g as u64 * KINDS + k as u64) * LIMBS) + (b as u64 >> 6)) << 6) + (b as u64 & 63);
        }
        return c;
    };
    let mut replay_rows = Vec::new();
    let mut other_rows = Vec::new();
    for r in records(&program).iter().filter(|r| r[0] == ROW) {
        let col = u32::from_be_bytes(r[1..5].try_into().unwrap());
        let na = u16::from_be_bytes(r[5..7].try_into().unwrap()) as usize;
        let cols: Vec<u64> = r[9..].chunks(4).map(|c| remap(u32::from_be_bytes(c.try_into().unwrap()))).collect();
        let row = (remap(col), cols[..na].to_vec(), cols[na..].to_vec());
        if (col as u64) >= base && (col as u64) < end {
            replay_rows.push(row);
        } else {
            other_rows.push(row);
        }
    }
    analyse("uniform block, stream rows of the replay", &replay_rows);
    analyse("uniform block, other stream rows", &other_rows);
}

fn report_words(name: &str, origins: &[(u32, u8, u16)]) {
    let mut kinds: HashMap<(u32, u8, u16), usize> = HashMap::new();
    for o in origins {
        *kinds.entry((o.0, o.1, o.2 >> 6)).or_insert(0) += 1;
    }
    println!(
        "{name}: {} gate-kind-limb words for {} columns ({} bits of head)",
        kinds.len(),
        origins.len(),
        kinds.len() * 64
    );
}
