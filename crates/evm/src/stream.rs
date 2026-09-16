// SPDX-License-Identifier: LGPL-3.0-or-later

//! The explicit-row stream of a block with its regular row families folded into single records,
//! which the contract sums in closed form.
//!
//! - a **row** record is one explicit row: its column, its A-side and B-side lengths and columns;
//! - an **identity** record stands for every row of the words `[w0, w1)` whose A side is its own
//!   column and whose B side is the constant wire;
//! - a **PRG** record stands for all the link rows of one slot's PRG sub-blocks;
//! - a **sponge** record stands for the constant-wire B side of all the link rows of one slot's
//!   sponge sub-blocks and for their links to the previous permutation's output, their preimage
//!   parts staying as row records with an empty B side.
//!
//! Every row a family record stands for is checked against the block when the stream is built,
//! so a stream that builds is the block's rows.

use pofseed_flock_lift_block::{
    form::CONST,
    layout::{Geometry, SubKind, h_col},
    program::Program,
};
use zkboo::crypto::TAG_PRG;

/// Record tags.
pub const ROW: u8 = 0;
/// Identity-word record tag.
pub const IDENTITY: u8 = 1;
/// PRG-family record tag.
pub const PRG: u8 = 2;
/// Sponge-family record tag.
pub const SPONGE: u8 = 3;

/// Bits of the PRG link preimage before its padding: tag, key digest and counter.
const PRG_BITS: usize = 9 * 8 + 256 + 64;

fn sorted(mut v: Vec<u32>) -> Vec<u32> {
    v.sort_unstable();
    return v;
}

/// The A side of PRG link row `p` of block `i` of slot `s`.
pub fn prg_form(g: &Geometry, s: usize, i: usize, p: usize) -> Vec<u32> {
    let mut cols = Vec::new();
    if p < 72 {
        if (TAG_PRG[p / 8] >> (p % 8)) & 1 == 1 {
            cols.push(CONST);
        }
    } else if p < 328 {
        cols.push(g.state24_col(s, SubKind::Key, p - 72));
    } else if p < PRG_BITS {
        let q = p - 328;
        let bit = |c: usize| (c >> q) & 1 == 1;
        let (c, diff) = if i < g.in_blocks() {
            (bit(i), false)
        } else {
            let j = i - g.in_blocks();
            (bit(j), bit(j) != bit(j + g.in_blocks()))
        };
        if c {
            cols.push(CONST);
        }
        if diff {
            cols.push(h_col(0));
            cols.push(h_col(1 + s));
        }
    } else if p == PRG_BITS || p == 1087 {
        cols.push(CONST);
    }
    return sorted(cols);
}

/// Which family, if any, a row belongs to: `(kind, slot, block)`.
fn family(g: &Geometry, col: u32) -> Option<(SubKind, usize)> {
    let sub = (col >> 16) as usize;
    if sub < g.head_subs() {
        return None;
    }
    let local = sub - g.head_subs();
    let slot = local / g.subs_per_slot();
    let within = local % g.subs_per_slot();
    return if within == 0 {
        None
    } else if within <= g.prg_blocks() {
        Some((SubKind::Prg(within - 1), slot))
    } else {
        Some((SubKind::Sponge(within - 1 - g.prg_blocks()), slot))
    };
}

fn push_row(out: &mut Vec<u8>, col: u32, a: &[u32], b: &[u32]) {
    out.push(ROW);
    out.extend_from_slice(&col.to_be_bytes());
    out.extend_from_slice(&(a.len() as u16).to_be_bytes());
    out.extend_from_slice(&(b.len() as u16).to_be_bytes());
    for &c in a.iter().chain(b) {
        out.extend_from_slice(&c.to_be_bytes());
    }
}

/// The stream of `program`, as a list of records.
pub fn records(program: &Program) -> Vec<Vec<u8>> {
    let g = program.geometry();
    let n = program.explicit_rows();
    let mut out = Vec::new();
    let mut families = [[false; 2]; 2];
    let mut identity: Vec<u32> = Vec::new();
    for r in 0..n {
        let (col, a, b) = program.explicit_row(r);
        match family(g, col) {
            Some((SubKind::Prg(i), s)) => {
                let p = (col & 0xffff) as usize;
                assert_eq!(a, prg_form(g, s, i, p).as_slice(), "PRG link row {r}");
                assert_eq!(b, [CONST], "PRG link row {r}");
                if !families[0][s] {
                    families[0][s] = true;
                    out.push(vec![PRG, s as u8]);
                }
            }
            Some((SubKind::Sponge(blk), s)) => {
                let p = (col & 0xffff) as usize;
                assert_eq!(b, [CONST], "sponge link row {r}");
                let mut pre: Vec<u32> = a.to_vec();
                if blk > 0 {
                    let link = g.state24_col(s, SubKind::Sponge(blk - 1), p);
                    let at = pre.iter().position(|&c| c == link).expect("the sponge link is on the A side");
                    pre.remove(at);
                }
                let sponge_output = |c: u32| matches!(family(g, c), Some((SubKind::Sponge(_), _)));
                assert!(!pre.iter().any(|&c| sponge_output(c)), "sponge preimage row {r}");
                if !families[1][s] {
                    families[1][s] = true;
                    out.push(vec![SPONGE, s as u8]);
                }
                if !pre.is_empty() {
                    let mut rec = Vec::new();
                    push_row(&mut rec, col, &pre, &[]);
                    out.push(rec);
                }
            }
            _ => {
                if col != CONST && a == [col] && b == [CONST] {
                    identity.push(col);
                } else {
                    let mut rec = Vec::new();
                    push_row(&mut rec, col, a, b);
                    out.push(rec);
                }
            }
        }
    }
    identity.sort_unstable();
    let mut i = 0;
    let mut words: Vec<u32> = Vec::new();
    while i < identity.len() {
        let c = identity[i];
        if c % 64 == 0 && i + 63 < identity.len() && identity[i + 63] == c + 63 {
            words.push(c / 64);
            i += 64;
        } else {
            let mut rec = Vec::new();
            push_row(&mut rec, c, &[c], &[CONST]);
            out.push(rec);
            i += 1;
        }
    }
    let mut w = 0;
    while w < words.len() {
        let start = words[w];
        let mut end = w;
        while end + 1 < words.len() && words[end + 1] == words[end] + 1 {
            end += 1;
        }
        let mut rec = vec![IDENTITY];
        rec.extend_from_slice(&start.to_be_bytes());
        rec.extend_from_slice(&(words[end] + 1).to_be_bytes());
        out.push(rec);
        w = end + 1;
    }
    for (kind, slots) in families.iter().enumerate() {
        assert!(slots.iter().all(|&f| f), "family {kind} is missing a slot");
    }
    return out;
}

/// Groups records into segments of at most `bytes` bytes each.
pub fn segments(records: &[Vec<u8>], bytes: usize) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = vec![Vec::new()];
    for rec in records {
        if out.last().expect("a segment").len() + rec.len() > bytes && !out.last().expect("a segment").is_empty() {
            out.push(Vec::new());
        }
        out.last_mut().expect("a segment").extend_from_slice(rec);
    }
    return out;
}
