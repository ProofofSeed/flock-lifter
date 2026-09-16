// SPDX-License-Identifier: LGPL-3.0-or-later

//! Measures how regular the block's explicit rows are: how many fall into periodic runs in which
//! every column below the fixed head shifts by one per period, and how those runs align with
//! the 64-bit word boundaries of the rows and columns, and what the contract's discharge stream
//! is left with once its row families are folded.

use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::stream::{ROW, records};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1};
use pofseed_flock_lift_statement::HardenedChildCircuit;

/// Columns below this are fixed wires (the constant, challenge bits and published words).
const FIXED: u32 = 32 * 128;

fn shifted(a: &[u32], b: &[u32], d: u32) -> bool {
    return a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| if x < FIXED { y == x } else { y == x + d });
}

fn matches(p: &Program, r: usize, k: usize, t: usize) -> bool {
    let (c0, a0, b0) = p.explicit_row(r);
    let (c, a, b) = p.explicit_row(r + k * t);
    return c == c0 + t as u32 && shifted(a0, a, t as u32) && shifted(b0, b, t as u32);
}

fn main() {
    let (_, chain_code) = bip32_vector_1();
    let program = Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET));
    let n = program.explicit_rows();
    let head = (program.geometry().head_subs() as u32) << 16;
    let mut covered = 0usize;
    let mut runs = 0usize;
    let mut aligned = 0usize;
    let mut loose = 0usize;
    let mut nnz_loose = 0usize;
    let mut period_rows = [0usize; 17];
    let mut r = 0;
    while r < n {
        if program.explicit_row(r).0 >= head {
            r += 1;
            continue;
        }
        let mut best = (0usize, 0usize);
        for k in 1..=16 {
            if r + k > n {
                break;
            }
            let mut t = 1;
            while t < 64 && r + k * (t + 1) <= n && (0..k).all(|j| matches(&program, r + j, k, t)) {
                t += 1;
            }
            if t * k > best.0 * best.1.max(1) && t >= 8 {
                best = (t, k);
            }
        }
        if best.0 >= 8 {
            let (t, k) = best;
            covered += t * k;
            runs += 1;
            period_rows[k] += t * k;
            let (c0, a0, b0) = program.explicit_row(r);
            if t == 64 && c0 % 64 == 0 && a0.iter().chain(b0).all(|&c| c < FIXED || c % 64 == 0) {
                aligned += t * k;
            }
            r += t * k;
        } else {
            let (_, a, b) = program.explicit_row(r);
            loose += 1;
            nnz_loose += a.len() + b.len();
            r += 1;
        }
    }
    if std::env::var_os("ROW_SAMPLE").is_some() {
        let start: usize = std::env::var("ROW_SAMPLE").unwrap().parse().unwrap();
        for r in start..start + 24 {
            let (c, a, b) = program.explicit_row(r);
            println!("row {r}: col {c} A {a:?} B {b:?}");
        }
    }
    println!("head rows in periodic runs: {covered} in {runs} runs, {aligned} of them word-aligned full runs");
    for (k, rows) in period_rows.iter().enumerate().filter(|&(_, &v)| v > 0) {
        println!("  period {k}: {rows} rows");
    }
    println!("head rows outside runs: {loose}, carrying {nnz_loose} nonzeros");
    let recs = records(&program);
    let rows: Vec<&Vec<u8>> = recs.iter().filter(|r| r[0] == ROW).collect();
    let refs: usize = rows.iter().map(|r| (r.len() - 9) / 4).sum();
    let bytes: usize = recs.iter().map(|r| r.len()).sum();
    println!(
        "stream: {} records, {} of them rows carrying {refs} column references, {bytes} bytes",
        recs.len(),
        rows.len()
    );
}
