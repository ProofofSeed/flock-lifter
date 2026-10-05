// SPDX-License-Identifier: LGPL-3.0-or-later

//! Prints the shape and sparsity of the hardened-child response block: its geometry, how many
//! explicit rows it has, how many nonzeros those rows carry, and how many committed entries they
//! become.

use std::time::Instant;

use pofseed_flock_lift_block::{committed::entries, keccak::SUB_BITS, program::Program};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1};
use pofseed_flock_lift_statement::HardenedChildCircuit;

fn main() {
    let (_, chain_code) = bip32_vector_1();
    let public = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let t = Instant::now();
    let program = Program::new(&public);
    let g = program.geometry();
    let (nnz_a, nnz_b) = program.explicit_nnz();
    println!("block built in {:.2} s", t.elapsed().as_secs_f64());
    println!("k_log                  {}", g.k_log());
    println!("sub-blocks             {} ({} head, {} Keccak-f)", 1 << (g.k_log() - 16), g.head_subs(), g.keccak_subs());
    println!("head bits              {}", g.head_subs() * SUB_BITS);
    println!("PRG blocks per slot    {}", g.prg_blocks());
    println!("sponge blocks per slot {}", g.sponge_blocks());
    println!("replay products        {}", program.replay_products());
    println!("replay materialised    {}", program.replay_materialised());
    println!("explicit rows          {}", program.explicit_rows());
    println!("explicit nonzeros      {} on A, {} on B ({} total)", nnz_a, nnz_b, nnz_a + nnz_b);
    println!(
        "nonzeros per row       {:.2} on A, {:.2} on B",
        nnz_a as f64 / program.explicit_rows() as f64,
        nnz_b as f64 / program.explicit_rows() as f64
    );
    let list = entries(&program);
    println!("committed entries      {}", list.len());
    let (mut full, mut fixed, mut b_side, mut absolute_words) = (0usize, 0usize, 0usize, std::collections::BTreeSet::new());
    for &e in &list {
        let address = (e >> 45) as usize;
        let (u, j) = (address / 128, address % 128);
        full += usize::from(j == 64);
        fixed += usize::from(u >= 64);
        b_side += (e & 1) as usize;
        if u >= 64 {
            absolute_words.insert((e >> 23) & ((1 << 22) - 1));
        }
    }
    let ops = pofseed_flock_lift_block::committed::operations(&program);
    println!(
        "operations             {} ({} at a fixed column bit, {} on B, {} over all 64 rows)",
        ops.len(),
        ops.iter().filter(|o| o.fixed).count(),
        ops.iter().filter(|o| o.side == 1).count(),
        ops.iter().filter(|o| o.mask == u64::MAX).count()
    );
    println!(
        "entries by kind       {full} full runs, {} partial; {fixed} at a fixed column bit ({} column words); {b_side} on B",
        list.len() - full,
        absolute_words.len()
    );
}
