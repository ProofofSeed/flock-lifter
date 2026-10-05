// SPDX-License-Identifier: LGPL-3.0-or-later

//! Keccak-f[1600] as a sub-block of the response block: lane primitives, the sub-block layout,
//! its native witness, and the fold of the rows every sub-block shares.
//!
//! The encoding is the one of the Keccak encoder Flock retired at revision `0f0d632`
//! (MIT OR Apache-2.0, Succinct Labs): only the input state, the output state and the 24 χ
//! outputs are committed, and every intermediate state is the linear substitution
//! `state_r = φ^r·state_0 ⊕ Σ_{i<r} φ^{r−1−i}·t_i ⊕ RC_r` with `φ = π∘ρ∘θ`.
//! Two things differ: the input-state rows are not self-loops but links to wherever the input
//! state comes from, and the constant wire is the block's rather than the sub-block's.

use flock_prover::field::F128;

/// log2 of the sub-block width.
pub const SUB_LOG: usize = 16;

/// Sub-block width in bits.
pub const SUB_BITS: usize = 1 << SUB_LOG;

/// Keccak-f state width in bits.
pub const STATE_BITS: usize = 1600;

/// Number of Keccak-f rounds.
pub const N_ROUNDS: usize = 24;

/// Local offset of the input state.
pub const STATE0_BASE: usize = 0;

/// Local offset of the output state.
pub const STATE24_BASE: usize = 2048;

/// Local offset of the first χ output.
pub const T_BASE: usize = 4160;

/// Local bits in use.
pub const USEFUL_BITS: usize = T_BASE + N_ROUNDS * STATE_BITS;

/// Keccak-f state as 25 lanes, lane `x + 5y`, bit `z` of a lane at bit `z` of its word.
pub type Lanes = [u64; 25];

const RHO_OFFSETS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// Keccak-f round constants.
pub const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// State bit index `x + 5y + 25z`.
#[inline]
pub fn state_idx(x: usize, y: usize, z: usize) -> usize {
    return x + 5 * y + 25 * z;
}

/// Offset of state bit `j` within a lane-contiguous 1600-bit region, which is also its bit
/// position in the little-endian byte serialisation of the state.
#[inline]
pub fn lane_pos(j: usize) -> usize {
    return 64 * (j % 25) + j / 25;
}

/// Local position of bit `j` of χ output `r`.
#[inline]
pub fn t_pos(r: usize, j: usize) -> usize {
    return T_BASE + r * STATE_BITS + lane_pos(j);
}

/// The 11 input-state bits whose XOR is bit `(x, y, z)` of `(π∘ρ∘θ)(state)`.
pub fn theta_rho_pi_preimage(x: usize, y: usize, z: usize) -> [usize; 11] {
    let a = (x + 3 * y) % 5;
    let b = x;
    let r = (RHO_OFFSETS[a][b] as usize) % 64;
    let c = (z + 64 - r) % 64;
    let c_prev = (c + 63) % 64;
    let a_minus = (a + 4) % 5;
    let a_plus = (a + 1) % 5;
    let mut bits = [0usize; 11];
    bits[0] = state_idx(a, b, c);
    for yp in 0..5 {
        bits[1 + yp] = state_idx(a_minus, yp, c);
    }
    for yp in 0..5 {
        bits[6 + yp] = state_idx(a_plus, yp, c_prev);
    }
    return bits;
}

/// θ on lanes.
#[inline]
fn theta_lanes(s: &mut Lanes) {
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20];
    }
    for x in 0..5 {
        let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            s[x + 5 * y] ^= d;
        }
    }
}

/// ρ∘π on lanes.
#[inline]
fn rho_pi_lanes(s_in: &Lanes) -> Lanes {
    let mut s_out = [0u64; 25];
    for y in 0..5 {
        for x in 0..5 {
            let a = (x + 3 * y) % 5;
            let b = x;
            s_out[x + 5 * y] = s_in[a + 5 * b].rotate_left(RHO_OFFSETS[a][b] % 64);
        }
    }
    return s_out;
}

/// Keccak-f[1600] on lanes.
pub fn keccak_f(s: &mut Lanes) {
    for r in 0..N_ROUNDS {
        theta_lanes(s);
        let b = rho_pi_lanes(s);
        for y in 0..5 {
            for x in 0..5 {
                s[x + 5 * y] = b[x + 5 * y] ^ ((!b[(x + 1) % 5 + 5 * y]) & b[(x + 2) % 5 + 5 * y]);
            }
        }
        s[0] ^= ROUND_CONSTANTS[r];
    }
}

/// Writes one sub-block's witness from its input state into local `z`, `a` and `b` words, which
/// must be zero on entry, and returns the output state.
pub fn write_witness(initial: &Lanes, z: &mut [u64], a: &mut [u64], b: &mut [u64]) -> Lanes {
    debug_assert_eq!(z.len(), SUB_BITS / 64);
    let s0 = STATE0_BASE / 64;
    for l in 0..25 {
        z[s0 + l] = initial[l];
        a[s0 + l] = initial[l];
        b[s0 + l] = u64::MAX;
    }
    let mut state = *initial;
    for r in 0..N_ROUNDS {
        let mut th = state;
        theta_lanes(&mut th);
        let bs = rho_pi_lanes(&th);
        let tb = T_BASE / 64 + r * 25;
        for y in 0..5 {
            for x in 0..5 {
                let l = x + 5 * y;
                let na = !bs[(x + 1) % 5 + 5 * y];
                let nb = bs[(x + 2) % 5 + 5 * y];
                z[tb + l] = na & nb;
                a[tb + l] = na;
                b[tb + l] = nb;
                state[l] = bs[l] ^ (na & nb);
            }
        }
        state[0] ^= ROUND_CONSTANTS[r];
    }
    let s24 = STATE24_BASE / 64;
    for l in 0..25 {
        z[s24 + l] = state[l];
        a[s24 + l] = state[l];
        b[s24 + l] = u64::MAX;
    }
    return state;
}

/// `out[s] = Σ_{s' : s ∈ preimage(s')} v[s']`: the transpose of `φ`.
fn apply_phi_t(v: &[F128]) -> Vec<F128> {
    let mut out = vec![F128::ZERO; STATE_BITS];
    for s_out in 0..STATE_BITS {
        let val = v[s_out];
        let preim = theta_rho_pi_preimage(s_out % 25 % 5, (s_out % 25) / 5, s_out / 25);
        for &s_in in &preim {
            out[s_in] += val;
        }
    }
    return out;
}

/// `φ` on a field-valued state indexed by `state_idx`.
fn apply_phi(v: &[F128]) -> Vec<F128> {
    return (0..STATE_BITS)
        .map(|s_out| {
            theta_rho_pi_preimage(s_out % 25 % 5, (s_out % 25) / 5, s_out / 25)
                .iter()
                .fold(F128::ZERO, |acc, &s| acc + v[s])
        })
        .collect();
}

/// The shared rows applied to column weights on side `A` (`a_side`) or `B`:
/// `out[p] = Σ_c M[p, c]·w[c] + M[p, const]·w_konst` over the local columns `w` and the constant
/// wire's weight, the adjoint of [`fold_shared`].
pub fn row_fold(a_side: bool, w: &[F128], w_konst: F128) -> Vec<F128> {
    debug_assert_eq!(w.len(), SUB_BITS);
    let at = |r: usize| -> Vec<F128> { (0..STATE_BITS).map(|s| w[t_pos(r, s)]).collect() };
    let mut g: Vec<Vec<F128>> = Vec::with_capacity(N_ROUNDS);
    g.push((0..STATE_BITS).map(|s| w[STATE0_BASE + lane_pos(s)]).collect());
    for r in 1..N_ROUNDS {
        let mut next = apply_phi(&g[r - 1]);
        for (n, x) in next.iter_mut().zip(at(r - 1)) {
            *n += x;
        }
        g.push(next);
    }
    let phi_g: Vec<Vec<F128>> = g.iter().map(|v| apply_phi(v)).collect();
    let bit = |b: bool| if b { F128::ONE } else { F128::ZERO };
    let mut out = vec![F128::ZERO; SUB_BITS];
    let mut rc = [false; STATE_BITS];
    for r in 0..N_ROUNDS {
        let rc_phi = apply_phi_bool(&rc);
        for zp in 0..64 {
            for y in 0..5 {
                for x in 0..5 {
                    let src = state_idx(if a_side { (x + 1) % 5 } else { (x + 2) % 5 }, y, zp);
                    let mut v = phi_g[r][src] + w_konst * bit(rc_phi[src]);
                    if a_side {
                        v += w_konst;
                    }
                    out[t_pos(r, state_idx(x, y, zp))] = v;
                }
            }
        }
        rc = rc_phi;
        for zp in 0..64 {
            if (ROUND_CONSTANTS[r] >> zp) & 1 == 1 {
                rc[state_idx(0, 0, zp)] ^= true;
            }
        }
    }
    let last = at(N_ROUNDS - 1);
    for s in 0..STATE_BITS {
        out[STATE24_BASE + lane_pos(s)] =
            if a_side { last[s] + w_konst * bit(rc[s]) + phi_g[N_ROUNDS - 1][s] } else { w_konst };
    }
    return out;
}

/// `φ` on a Boolean state indexed by `state_idx`.
fn apply_phi_bool(v: &[bool; STATE_BITS]) -> [bool; STATE_BITS] {
    let mut out = [false; STATE_BITS];
    for s_out in 0..STATE_BITS {
        let preim = theta_rho_pi_preimage(s_out % 25 % 5, (s_out % 25) / 5, s_out / 25);
        out[s_out] = preim.iter().fold(false, |acc, &s| acc ^ v[s]);
    }
    return out;
}

/// Adds `α·(eqᵀ·A_S) + eqᵀ·B_S` into `comb` over the sub-block's local columns, where `A_S` and
/// `B_S` are the shared rows (the χ rows and the output-state pins) and `eq` their local row
/// weights, and returns the part of the fold that lands on the constant wire.
pub fn fold_shared(alpha: F128, eq: &[F128], comb: &mut [F128]) -> F128 {
    debug_assert_eq!(eq.len(), SUB_BITS);
    debug_assert_eq!(comb.len(), SUB_BITS);
    let mut konst = F128::ZERO;
    let mut vec_pin = vec![F128::ZERO; STATE_BITS];
    for j in 0..STATE_BITS {
        let e = eq[STATE24_BASE + lane_pos(j)];
        vec_pin[j] = e;
        konst += e;
    }
    let mut chi_a: Vec<Vec<F128>> = (0..N_ROUNDS).map(|_| vec![F128::ZERO; STATE_BITS]).collect();
    let mut chi_b: Vec<Vec<F128>> = (0..N_ROUNDS).map(|_| vec![F128::ZERO; STATE_BITS]).collect();
    let mut sum_eq_t = F128::ZERO;
    for r in 0..N_ROUNDS {
        for zp in 0..64 {
            for y in 0..5 {
                for x in 0..5 {
                    let e = eq[t_pos(r, state_idx(x, y, zp))];
                    sum_eq_t += e;
                    for &s in &theta_rho_pi_preimage((x + 1) % 5, y, zp) {
                        chi_a[r][s] += e;
                    }
                    for &s in &theta_rho_pi_preimage((x + 2) % 5, y, zp) {
                        chi_b[r][s] += e;
                    }
                }
            }
        }
    }
    konst += alpha * sum_eq_t;
    let mut rc = [false; STATE_BITS];
    let mut rc_a = F128::ZERO;
    let mut rc_b = F128::ZERO;
    for r in 0..N_ROUNDS {
        for s in 0..STATE_BITS {
            if rc[s] {
                rc_a += chi_a[r][s];
                rc_b += chi_b[r][s];
            }
        }
        rc = apply_phi_bool(&rc);
        for zp in 0..64 {
            if (ROUND_CONSTANTS[r] >> zp) & 1 == 1 {
                rc[state_idx(0, 0, zp)] ^= true;
            }
        }
    }
    let mut rc_pin = F128::ZERO;
    for s in 0..STATE_BITS {
        if rc[s] {
            rc_pin += vec_pin[s];
        }
    }
    konst += alpha * rc_a + rc_b + alpha * rc_pin;
    for s in 0..STATE_BITS {
        comb[t_pos(N_ROUNDS - 1, s)] += alpha * vec_pin[s];
    }
    let mut k_a = apply_phi_t(&vec_pin);
    for s in 0..STATE_BITS {
        k_a[s] += chi_a[N_ROUNDS - 1][s];
    }
    for r in (1..N_ROUNDS).rev() {
        for s in 0..STATE_BITS {
            comb[t_pos(r - 1, s)] += alpha * k_a[s];
        }
        let mut next = apply_phi_t(&k_a);
        for s in 0..STATE_BITS {
            next[s] += chi_a[r - 1][s];
        }
        k_a = next;
    }
    for s in 0..STATE_BITS {
        comb[STATE0_BASE + lane_pos(s)] += alpha * k_a[s];
    }
    let mut k_b = chi_b[N_ROUNDS - 1].clone();
    for r in (1..N_ROUNDS).rev() {
        for s in 0..STATE_BITS {
            comb[t_pos(r - 1, s)] += k_b[s];
        }
        let mut next = apply_phi_t(&k_b);
        for s in 0..STATE_BITS {
            next[s] += chi_b[r - 1][s];
        }
        k_b = next;
    }
    for s in 0..STATE_BITS {
        comb[STATE0_BASE + lane_pos(s)] += k_b[s];
    }
    return konst;
}

/// Word of χ output lane `lane` of round `r` in a sub-block.
pub fn t_word(r: usize, lane: usize) -> usize {
    return T_BASE / 64 + 25 * r + lane;
}

/// `K[d] = Σ_u skip[u]·z[(u + d) mod 64]`: how a unit kernel at shift `d` pairs with the row bit
/// weights `skip` and the column bit weights `z`.
pub fn shift_pairing(skip: &[F128], z: &[F128]) -> Vec<F128> {
    return (0..64)
        .map(|d| (0..64).fold(F128::ZERO, |acc, u| acc + skip[u] * z[(u + d) % 64]))
        .collect();
}

/// The shared fold of [`fold_shared`] under local row weights `skip[p & 63]·row[p >> 6]`, paired
/// with local column weights `col[c >> 6]·z[c & 63]`, and its constant-wire part, computed in
/// rotation-invariant form.
///
/// Every map in the fold commutes with rotating all lanes together, so the fold of such row
/// weights is, lane by lane, the row bit weights convolved with a kernel. The kernel is the fold
/// of the row word weights alone, placed at bit 0 of each lane, which only reaches the positions
/// its few inputs spread to; the pairing with the columns is then the kernel paired with
/// [`shift_pairing`]. The round constants enter the fold's constant-wire part exactly where the
/// χ outputs of their round enter the columns, so that part is the round constants' bits paired
/// with the same kernels.
pub fn fold_shared_paired(alpha: F128, skip: &[F128], row: &[F128], z: &[F128], col: &[F128]) -> (F128, F128) {
    let lanes = STATE_BITS / 64;
    let pair = shift_pairing(skip, z);
    let lane_dot = |v: &[F128], lane: usize, w: &[F128]| (0..64).fold(F128::ZERO, |acc, d| acc + v[lane + 25 * d] * w[d]);
    let mut chi = vec![vec![F128::ZERO; STATE_BITS]; N_ROUNDS];
    let mut weights = F128::ZERO;
    for r in 0..N_ROUNDS {
        for y in 0..5 {
            for x in 0..5 {
                let e = row[t_word(r, x + 5 * y)];
                weights += e;
                let ae = alpha * e;
                for &s in &theta_rho_pi_preimage((x + 1) % 5, y, 0) {
                    chi[r][s] += ae;
                }
                for &s in &theta_rho_pi_preimage((x + 2) % 5, y, 0) {
                    chi[r][s] += e;
                }
            }
        }
    }
    let mut kernel = vec![F128::ZERO; STATE_BITS];
    let mut pins = F128::ZERO;
    for lane in 0..lanes {
        let e = row[STATE24_BASE / 64 + lane];
        kernel[lane] = alpha * e;
        pins += e;
    }
    let skip_sum = skip.iter().fold(F128::ZERO, |a, &b| a + b);
    let mut konst = skip_sum * (pins + alpha * weights);
    let mut value = F128::ZERO;
    let round_constant = |r: usize, kernel: &[F128], konst: &mut F128| {
        let mut w = vec![F128::ZERO; 64];
        for (d, wd) in w.iter_mut().enumerate() {
            for c in 0..64 {
                if (ROUND_CONSTANTS[r] >> c) & 1 == 1 {
                    *wd += skip[(c + 64 - d) % 64];
                }
            }
        }
        *konst += lane_dot(kernel, 0, &w);
    };
    for r in (0..N_ROUNDS).rev() {
        for lane in 0..lanes {
            value += col[t_word(r, lane)] * lane_dot(&kernel, lane, &pair);
        }
        round_constant(r, &kernel, &mut konst);
        let mut next = apply_phi_t(&kernel);
        for (n, c) in next.iter_mut().zip(&chi[r]) {
            *n += *c;
        }
        kernel = next;
    }
    for lane in 0..lanes {
        value += col[STATE0_BASE / 64 + lane] * lane_dot(&kernel, lane, &pair);
    }
    return (value, konst);
}

#[cfg(test)]
mod tests {
    use super::*;

    const WORDS: usize = SUB_BITS / 64 + 1;
    const CONST_BIT: usize = SUB_BITS;

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            return self.0;
        }

        fn f128(&mut self) -> F128 {
            return F128::new(self.next(), self.next());
        }
    }

    type Bits = Vec<u64>;

    fn bits_col(c: usize) -> Bits {
        let mut v = vec![0u64; WORDS];
        v[c / 64] |= 1 << (c % 64);
        return v;
    }

    fn xor_into(dst: &mut Bits, src: &Bits) {
        dst.iter_mut().zip(src).for_each(|(d, s)| *d ^= s);
    }

    /// The shared rows as dense bitsets, by forward substitution: `(row, A, B)`.
    fn shared_rows() -> Vec<(usize, Bits, Bits)> {
        let mut state: Vec<Bits> = (0..STATE_BITS).map(|j| bits_col(STATE0_BASE + lane_pos(j))).collect();
        let konst = bits_col(CONST_BIT);
        let mut rows = Vec::new();
        for r in 0..N_ROUNDS {
            let bstate: Vec<Bits> = (0..STATE_BITS)
                .map(|s| {
                    let mut acc = vec![0u64; WORDS];
                    for &p in &theta_rho_pi_preimage(s % 5, (s / 5) % 5, s / 25) {
                        xor_into(&mut acc, &state[p]);
                    }
                    acc
                })
                .collect();
            let mut next = Vec::with_capacity(STATE_BITS);
            for s in 0..STATE_BITS {
                let (x, y, zp) = (s % 5, (s / 5) % 5, s / 25);
                let mut a = bstate[state_idx((x + 1) % 5, y, zp)].clone();
                xor_into(&mut a, &konst);
                let b = bstate[state_idx((x + 2) % 5, y, zp)].clone();
                rows.push((t_pos(r, s), a, b));
                let mut n = bstate[s].clone();
                xor_into(&mut n, &bits_col(t_pos(r, s)));
                next.push(n);
            }
            for zp in 0..64 {
                if (ROUND_CONSTANTS[r] >> zp) & 1 == 1 {
                    xor_into(&mut next[state_idx(0, 0, zp)], &konst);
                }
            }
            state = next;
        }
        for j in 0..STATE_BITS {
            rows.push((STATE24_BASE + lane_pos(j), state[j].clone(), konst.clone()));
        }
        return rows;
    }

    fn parity_and(x: &Bits, z: &Bits) -> bool {
        return x.iter().zip(z).map(|(a, b)| (a & b).count_ones()).sum::<u32>() & 1 == 1;
    }

    #[test]
    fn keccak_f_is_keccak_256() {
        use tiny_keccak::{Hasher, Keccak};
        let msg: Vec<u8> = (0..49u8).map(|i| i.wrapping_mul(37) ^ 0x5a).collect();
        let mut expected = [0u8; 32];
        let mut k = Keccak::v256();
        k.update(&msg);
        k.finalize(&mut expected);
        let mut bytes = [0u8; 200];
        bytes[..49].copy_from_slice(&msg);
        bytes[49] ^= 0x01;
        bytes[135] ^= 0x80;
        let mut lanes = [0u64; 25];
        for l in 0..25 {
            lanes[l] = u64::from_le_bytes(bytes[8 * l..8 * l + 8].try_into().unwrap());
        }
        keccak_f(&mut lanes);
        let out: Vec<u8> = lanes[..4].iter().flat_map(|l| l.to_le_bytes()).collect();
        assert_eq!(out, expected);
    }

    #[test]
    fn witness_satisfies_the_shared_rows() {
        let mut rng = Rng(0x1234_5678_9abc_def1);
        let initial: Lanes = core::array::from_fn(|_| rng.next());
        let (mut z, mut a, mut b) = (vec![0u64; SUB_BITS / 64], vec![0u64; SUB_BITS / 64], vec![0u64; SUB_BITS / 64]);
        let out = write_witness(&initial, &mut z, &mut a, &mut b);
        let mut expected = initial;
        keccak_f(&mut expected);
        assert_eq!(out, expected);
        let mut zc = z.clone();
        zc.push(1);
        let get = |v: &[u64], i: usize| (v[i / 64] >> (i % 64)) & 1 == 1;
        for (row, ra, rb) in shared_rows() {
            let pa = parity_and(&ra, &zc);
            let pb = parity_and(&rb, &zc);
            assert_eq!(get(&a, row), pa, "a at {row}");
            assert_eq!(get(&b, row), pb, "b at {row}");
            assert_eq!(get(&z, row), pa & pb, "z at {row}");
        }
    }

    #[test]
    fn fold_matches_the_substituted_rows() {
        let mut rng = Rng(0x0bad_cafe_f00d_d00d);
        let alpha = rng.f128();
        let eq: Vec<F128> = (0..SUB_BITS).map(|_| rng.f128()).collect();
        let mut comb = vec![F128::ZERO; SUB_BITS];
        let konst = fold_shared(alpha, &eq, &mut comb);
        let mut expected = vec![F128::ZERO; SUB_BITS + 1];
        for (row, ra, rb) in shared_rows() {
            let e = eq[row];
            for (w, (&wa, &wb)) in ra.iter().zip(&rb).enumerate() {
                for bit in 0..64 {
                    let c = 64 * w + bit;
                    if (wa >> bit) & 1 == 1 {
                        expected[c] += alpha * e;
                    }
                    if (wb >> bit) & 1 == 1 {
                        expected[c] += e;
                    }
                }
            }
        }
        assert_eq!(konst, expected[CONST_BIT]);
        assert_eq!(&comb[..], &expected[..SUB_BITS]);
    }

    #[test]
    fn paired_fold_matches_the_dense_fold() {
        let mut rng = Rng(0x5eed_1234_abcd_0001);
        let alpha = rng.f128();
        let skip: Vec<F128> = (0..64).map(|_| rng.f128()).collect();
        let z: Vec<F128> = (0..64).map(|_| rng.f128()).collect();
        let row: Vec<F128> = (0..SUB_BITS / 64).map(|_| rng.f128()).collect();
        let col: Vec<F128> = (0..SUB_BITS / 64).map(|_| rng.f128()).collect();
        let eq: Vec<F128> = (0..SUB_BITS).map(|p| skip[p & 63] * row[p >> 6]).collect();
        let mut comb = vec![F128::ZERO; SUB_BITS];
        let konst = fold_shared(alpha, &eq, &mut comb);
        let value = (0..SUB_BITS).fold(F128::ZERO, |acc, c| acc + comb[c] * col[c >> 6] * z[c & 63]);
        assert_eq!(fold_shared_paired(alpha, &skip, &row, &z, &col), (value, konst));
    }

    /// The transpose of `φ` on a lane-major vector (`lane·64 + bit`): the inverse of π∘ρ, then
    /// the transpose of θ through column sums.
    fn phi_t_lane_major(v: &[F128]) -> Vec<F128> {
        let mut w = vec![F128::ZERO; STATE_BITS];
        for a in 0..5 {
            for b in 0..5 {
                let y = (2 * (a + 5 - b)) % 5;
                let r = (RHO_OFFSETS[a][b] as usize) % 64;
                for c in 0..64 {
                    w[64 * (a + 5 * b) + c] = v[64 * (b + 5 * y) + (c + r) % 64];
                }
            }
        }
        let mut col = [[F128::ZERO; 64]; 5];
        for a in 0..5 {
            for b in 0..5 {
                for c in 0..64 {
                    col[a][c] += w[64 * (a + 5 * b) + c];
                }
            }
        }
        let mut out = w;
        for a in 0..5 {
            for c in 0..64 {
                let d = col[(a + 1) % 5][c] + col[(a + 4) % 5][(c + 1) % 64];
                for b in 0..5 {
                    out[64 * (a + 5 * b) + c] += d;
                }
            }
        }
        return out;
    }

    #[test]
    fn lane_major_phi_transpose_matches() {
        let mut rng = Rng(0x7070_1234_5678_9abc);
        let v: Vec<F128> = (0..STATE_BITS).map(|_| rng.f128()).collect();
        let lane_major: Vec<F128> = (0..STATE_BITS).map(|p| v[p / 64 + 25 * (p % 64)]).collect();
        let expected = apply_phi_t(&v);
        let got = phi_t_lane_major(&lane_major);
        for p in 0..STATE_BITS {
            assert_eq!(got[p], expected[p / 64 + 25 * (p % 64)], "position {p}");
        }
    }
}
