// SPDX-License-Identifier: LGPL-3.0-or-later

//! A small ZKBoo circuit exercising every gate kind the block compiles, for tests and probes.

use zkboo::{
    backend::{Backend, Frontend, WordRef},
    circuit::Circuit,
};

/// A circuit over 32 input bytes using every gate kind at widths 8, 32, 64 and 256.
pub struct Toy;

impl Circuit for Toy {
    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
        let bytes: Vec<WordRef<B, u8>> = (0..32u8).map(|i| frontend.input(i.wrapping_mul(7) ^ 0x33)).collect();
        let a = bytes[0].clone().bitand(bytes[1].clone());
        let b = bytes[2].clone().not().bitxor_const(0x5au8);
        let c = a.wrapping_add(b);
        let d = c.rotate_left(3).unbounded_shr(1).unbounded_shl(2).reverse_bits();
        let x = bytes[3].clone().cast::<u64>().rotate_left(13) ^ bytes[4].clone().cast::<u64>().swap_bytes();
        let y = x.clone().wrapping_add(bytes[5].clone().cast::<u64>().bitand_const(0xF0F0u64));
        let z = x.bitand(y.clone()).bitxor_const(0x0123_4567_89ab_cdefu64);
        let comp = WordRef::<B, u64, 4>::from_le_words([
            y.clone(),
            z.clone(),
            y.clone().not(),
            z.clone().rotate_right(7),
        ]);
        let comp2 = comp
            .clone()
            .wrapping_add(comp.clone().rotate_left(70))
            .bitand(comp.swap_bytes())
            .reverse_bits()
            .unbounded_shr(9);
        let small = z.cast::<u32>();
        let s2 = small.clone().bitand(small.clone().rotate_left(5)).cast::<u8>();
        frontend.output(d);
        frontend.output(s2);
        frontend.output(small);
        frontend.output(comp2);
        frontend.output(y);
        frontend.output(bytes[31].clone());
    }
}
