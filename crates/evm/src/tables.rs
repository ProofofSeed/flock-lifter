// SPDX-License-Identifier: LGPL-3.0-or-later

//! Reference versions of the contract's table-driven kernels, for testing them.

use flock_prover::field::F128;

fn v(x: F128) -> u128 {
    return ((x.hi as u128) << 64) | x.lo as u128;
}

/// `x·z` in GHASH form.
pub fn mulx(z: u128) -> u128 {
    return (z << 1) ^ if z >> 127 == 1 { 0x87 } else { 0 };
}

/// The rows of the matrix of multiplication by `q`: bit `j` of row `k` is bit `k` of `x^j·q`,
/// by the recurrence the contract uses.
pub fn masks(q: F128) -> [u128; 128] {
    let q = v(q);
    let rev = q.reverse_bits();
    let low = rev & 0x7f;
    let m127 = rev ^ (low << 121) ^ ((low & 3) << 126) ^ ((low & 1) << 127);
    let s = m127 << 1;
    let mut m = [0u128; 128];
    let mut prev = 0u128;
    for k in 0..128 {
        let feedback = if matches!(k, 0 | 1 | 2 | 7) { s } else { 0 };
        m[k] = (prev << 1) ^ feedback ^ ((q >> k) & 1);
        prev = m[k];
    }
    assert_eq!(m[127], m127, "the recurrence closes");
    return m;
}

/// The same rows, directly.
pub fn masks_naive(q: F128) -> [u128; 128] {
    let mut m = [0u128; 128];
    let mut vj = v(q);
    for j in 0..128 {
        for (k, row) in m.iter_mut().enumerate() {
            *row |= ((vj >> k) & 1) << j;
        }
        vj = mulx(vj);
    }
    return m;
}

/// Left multiplication of the tensor rows `rows` by `q`: `out[k] = Σ_i bit_i(m_k)·rows[i]`.
pub fn left_mul(rows: &[F128], q: F128) -> Vec<F128> {
    let m = masks(q);
    return (0..128)
        .map(|k| {
            (0..128).filter(|&i| (m[k] >> i) & 1 == 1).fold(F128::ZERO, |acc, i| acc + rows[i])
        })
        .collect();
}

/// Left multiplication by `x^-1`.
pub fn left_mul_x_inv(rows: &[F128]) -> Vec<F128> {
    return (0..128)
        .map(|k| {
            let next = if k < 127 { rows[k + 1] } else { F128::ZERO };
            if matches!(k, 0 | 1 | 6 | 127) { next + rows[0] } else { next }
        })
        .collect();
}

#[cfg(test)]
mod tests {
    use super::*;
    use flock_prover::pcs::tensor_algebra::TensorAlgebra;

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            return self.0;
        }
    }

    #[test]
    fn mask_recurrence_matches_the_definition() {
        let mut rng = Rng(0x1234_5678);
        for _ in 0..50 {
            let q = F128::new(rng.next(), rng.next());
            assert_eq!(masks(q), masks_naive(q));
        }
        assert_eq!(masks(F128::ONE), masks_naive(F128::ONE));
    }

    #[test]
    fn left_multiplication_is_the_horizontal_scaling() {
        let mut rng = Rng(0x9abc_def0);
        let rows: Vec<F128> = (0..128).map(|_| F128::new(rng.next(), rng.next())).collect();
        let q = F128::new(rng.next(), rng.next());
        let expected = TensorAlgebra { elems: rows.clone() }.scale_horizontal(q).elems;
        assert_eq!(left_mul(&rows, q), expected);
        let x_inv = flock_prover::field::QUADRATIC_NONRESIDUE;
        let expected = TensorAlgebra { elems: rows.clone() }.scale_horizontal(x_inv).elems;
        assert_eq!(left_mul_x_inv(&rows), expected);
    }
}
