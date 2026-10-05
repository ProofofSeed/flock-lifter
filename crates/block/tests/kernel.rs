// SPDX-License-Identifier: LGPL-3.0-or-later

//! The lane-level kernel of the shared Keccak-f rows against the structured fold it describes.

use flock_prover::{field::F128, lincheck::build_eq_table};
use pofseed_flock_lift_block::{
    kernel::{Kernel, WORD_LOG},
    program::{Program, product_range_sum},
    toy::Toy,
};

struct Rng(u64);

impl Rng {
    fn f128(&mut self) -> F128 {
        let mut next = || {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        };
        return F128::new(next(), next());
    }
}

#[test]
fn the_kernel_evaluates_the_shared_rows() {
    let program = Program::new(&Toy);
    let g = program.geometry();
    let k = g.k_log();
    let kernel = Kernel::new();
    println!("{} word kernels holding {} offsets, {} constant masks", kernel.words.len(), kernel.offsets(), kernel.constant.len());
    let mut rng = Rng(0x2468_ace0_1357_9bdf);
    for _ in 0..3 {
        let row: Vec<F128> = (0..k).map(|_| rng.f128()).collect();
        let col: Vec<F128> = (0..k).map(|_| rng.f128()).collect();
        let (a, b) = (build_eq_table(&row[..6]), build_eq_table(&col[..6]));
        let (xr, xc) = (build_eq_table(&row[6..6 + WORD_LOG]), build_eq_table(&col[6..6 + WORD_LOG]));
        let (rh, ch) = (&row[6 + WORD_LOG..], &col[6 + WORD_LOG..]);
        let range = (g.head_subs(), g.head_subs() + g.keccak_subs());
        let both: Vec<(F128, F128)> =
            rh.iter().zip(ch).map(|(&p, &q)| ((F128::ONE + p) * (F128::ONE + q), p * q)).collect();
        let rows: Vec<(F128, F128)> = rh.iter().map(|&p| (F128::ONE + p, p)).collect();
        let weight = product_range_sum(&both, range.0, range.1);
        let weight_rows = product_range_sum(&rows, range.0, range.1);
        let at_constant = col.iter().fold(F128::ONE, |acc, &c| acc * (F128::ONE + c));
        let pairing: Vec<F128> =
            (0..64).map(|d| (0..64).fold(F128::ZERO, |acc, z| acc + a[z] * b[(z + d) % 64])).collect();
        let mut by_side = [F128::ZERO; 2];
        for &(side, w, w2, mask) in &kernel.words {
            let offsets = (0..64).filter(|d| mask >> d & 1 == 1).fold(F128::ZERO, |acc, d| acc + pairing[d]);
            by_side[side as usize] += weight * xr[w as usize] * xc[w2 as usize] * offsets;
        }
        for &(side, w, mask) in &kernel.constant {
            let bits = (0..64).filter(|z| mask >> z & 1 == 1).fold(F128::ZERO, |acc, z| acc + a[z]);
            by_side[side as usize] += weight_rows * at_constant * xr[w as usize] * bits;
        }
        let structured = |alpha: F128| -> F128 {
            program
                .comb_structured(alpha, F128::ZERO, &a, &row[6..], &col[6..])
                .iter()
                .zip(&b)
                .fold(F128::ZERO, |acc, (&x, &e)| acc + x * e)
        };
        let on_b = structured(F128::ZERO);
        assert_eq!(by_side[1], on_b, "the B side");
        assert_eq!(by_side[0], structured(F128::ONE) + on_b, "the A side");
        assert!(by_side[0] != F128::ZERO && by_side[1] != F128::ZERO);
    }
}
