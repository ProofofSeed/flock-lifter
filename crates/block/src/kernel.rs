// SPDX-License-Identifier: LGPL-3.0-or-later

//! The rows every Keccak-f sub-block shares, at the level of lanes.
//!
//! Every map in those rows commutes with rotating all lanes together, so a row word reads a column
//! word through a polynomial in the rotation: bit `z` of the row word has column bit
//! `(z + d) mod 64` on a side exactly when the side's kernel for the two words has bit `d`. The
//! constant wire is read through a mask over the row word's bits instead.

use crate::keccak::{N_ROUNDS, ROUND_CONSTANTS, STATE0_BASE, STATE24_BASE, T_BASE, theta_rho_pi_preimage};

/// Lanes of the Keccak-f state.
pub const LANES: usize = 25;

/// log2 of the local words a kernel addresses.
pub const WORD_LOG: usize = 10;

/// A 25 by 25 matrix over `GF(2)[X]/(X^64 + 1)`, a polynomial held as the mask of its exponents.
type Lanes2 = [[u64; LANES]; LANES];

fn ring_mul(a: u64, b: u64) -> u64 {
    let mut acc = 0u64;
    let mut m = a;
    while m != 0 {
        acc ^= b.rotate_left(m.trailing_zeros());
        m &= m - 1;
    }
    return acc;
}

/// `φ = π∘ρ∘θ` on lanes: entry `[out][in]` is the polynomial `Σ X^r` over the rotations `r` by
/// which lane `in` enters lane `out`.
fn phi() -> Lanes2 {
    let mut m = [[0u64; LANES]; LANES];
    for y in 0..5 {
        for x in 0..5 {
            for s in theta_rho_pi_preimage(x, y, 0) {
                m[x + 5 * y][s % LANES] ^= 1 << ((64 - s / LANES) % 64);
            }
        }
    }
    return m;
}

fn mat_mul(a: &Lanes2, b: &Lanes2) -> Lanes2 {
    let mut out = [[0u64; LANES]; LANES];
    for i in 0..LANES {
        for k in 0..LANES {
            if a[i][k] == 0 {
                continue;
            }
            for j in 0..LANES {
                out[i][j] ^= ring_mul(a[i][k], b[k][j]);
            }
        }
    }
    return out;
}

/// Local word of input-state lane `lane`.
pub fn state0_word(lane: usize) -> usize {
    return STATE0_BASE / 64 + lane;
}

/// Local word of output-state lane `lane`.
pub fn state24_word(lane: usize) -> usize {
    return STATE24_BASE / 64 + lane;
}

/// Local word of χ output lane `lane` of round `r`.
pub fn t_word(r: usize, lane: usize) -> usize {
    return T_BASE / 64 + LANES * r + lane;
}

/// The shared rows of a Keccak-f sub-block at the level of lanes.
pub struct Kernel {
    /// Per side, row word and column word, the mask of the offsets `d`.
    pub words: Vec<(u8, u16, u16, u64)>,
    /// Per side and row word, the mask of the row bits that read the constant wire.
    pub constant: Vec<(u8, u16, u64)>,
}

impl Kernel {
    /// Builds the kernel.
    pub fn new() -> Self {
        let phi = phi();
        let mut powers: Vec<Lanes2> = Vec::with_capacity(N_ROUNDS + 1);
        let mut identity = [[0u64; LANES]; LANES];
        for (i, row) in identity.iter_mut().enumerate() {
            row[i] = 1;
        }
        powers.push(identity);
        for s in 1..=N_ROUNDS {
            powers.push(mat_mul(&phi, &powers[s - 1]));
        }
        // A polynomial `Σ X^d` takes bit `z − d` of its operand to bit `z`; an offset mask holds `−d`.
        let flip = |p: u64| p.reverse_bits().rotate_left(1);
        let mut words = Vec::new();
        let mut constant = Vec::new();
        // A row reading lane `lane` of `Φ^top·U_0 + Σ_{i<n} Φ^(top−1−i)·(t_i + RC_i·e_0)`, the state
        // before round `n` once `top − n` further `φ` are applied, plus one when `ones`.
        let mut row = |side: u8, row_word: usize, lane: usize, top: usize, n: usize, ones: bool| {
            let mut konst = if ones { u64::MAX } else { 0 };
            for (l, &p) in powers[top][lane].iter().enumerate() {
                if p != 0 {
                    words.push((side, row_word as u16, state0_word(l) as u16, flip(p)));
                }
            }
            for i in 0..n {
                let m = &powers[top - 1 - i][lane];
                for (l, &p) in m.iter().enumerate() {
                    if p != 0 {
                        words.push((side, row_word as u16, t_word(i, l) as u16, flip(p)));
                    }
                }
                konst ^= ring_mul(m[0], ROUND_CONSTANTS[i]);
            }
            if konst != 0 {
                constant.push((side, row_word as u16, konst));
            }
        };
        for r in 0..N_ROUNDS {
            for y in 0..5 {
                for x in 0..5 {
                    let w = t_word(r, x + 5 * y);
                    row(0, w, (x + 1) % 5 + 5 * y, r + 1, r, true);
                    row(1, w, (x + 2) % 5 + 5 * y, r + 1, r, false);
                }
            }
        }
        for lane in 0..LANES {
            row(0, state24_word(lane), lane, N_ROUNDS, N_ROUNDS, false);
        }
        constant.extend((0..LANES).map(|lane| (1, state24_word(lane) as u16, u64::MAX)));
        return Self { words, constant };
    }

    /// The entries of the word kernels.
    pub fn offsets(&self) -> usize {
        return self.words.iter().map(|w| w.3.count_ones() as usize).sum();
    }
}

impl Default for Kernel {
    fn default() -> Self {
        return Self::new();
    }
}
