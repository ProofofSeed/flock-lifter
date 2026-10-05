// SPDX-License-Identifier: LGPL-3.0-or-later
//! Reed–Solomon evaluation domains over GF(2^128): additive subspaces in the novel polynomial basis.

use flock_prover::field::F128;
use flock_prover::field::F256;
use flock_prover::ntt::additive_ntt_f128::AdditiveNttF128;
use rayon::prelude::*;

/// An additive evaluation domain of `2^log_size` points, spanned by `1, x, …, x^(log_size - 1)`.
pub struct Domain {
    log_size: usize,
    ntt: AdditiveNttF128,
    subspace: Vec<Vec<F128>>,
}

/// The normalised subspace polynomials on the basis: row `i` holds `Ŵ_i(β_i), Ŵ_i(β_(i+1)), …`.
fn subspace_table(basis: &[F128]) -> Vec<Vec<F128>> {
    let mut rows: Vec<Vec<F128>> = vec![basis.to_vec()];
    for i in 1..basis.len() {
        let prev = &rows[i - 1];
        let row: Vec<F128> = (1..prev.len()).map(|k| prev[k] * (prev[k] + prev[0])).collect();
        rows.push(row);
    }
    for row in rows.iter_mut() {
        let inv = row[0].inv();
        row.iter_mut().for_each(|v| *v *= inv);
    }
    rows
}

impl Domain {
    /// The domain of `2^log_size` points.
    pub fn new(log_size: usize) -> Domain {
        let basis: Vec<F128> = (0..log_size).map(|i| F128::new(1u64 << i, 0)).collect();
        Domain { log_size, ntt: AdditiveNttF128::new(&basis), subspace: subspace_table(&basis) }
    }

    /// The normalised subspace table: row `i` holds `Ŵ_i` at the basis elements `i, i + 1, …`.
    pub fn table(&self) -> &[Vec<F128>] {
        &self.subspace
    }

    /// Log of the number of points.
    pub fn log_size(&self) -> usize {
        self.log_size
    }

    /// Number of points.
    pub fn size(&self) -> usize {
        1 << self.log_size
    }

    /// The novel-basis coordinates `Ŵ_i(x)` of point `pos`, for `i < n`.
    pub fn coordinates(&self, pos: usize, n: usize) -> Vec<F128> {
        (0..n)
            .map(|i| {
                let mut acc = if (pos >> i) & 1 == 1 { F128::ONE } else { F128::ZERO };
                for j in i + 1..self.log_size {
                    if (pos >> j) & 1 == 1 {
                        acc += self.subspace[i][j - i];
                    }
                }
                acc
            })
            .collect()
    }

    /// Encodes `lanes` interleaved messages of `msg.len() / lanes` novel-basis coefficients each,
    /// laid out `msg[row * lanes + lane]`, into codewords laid out `word[pos * lanes + lane]`.
    pub fn encode(&self, msg: &[F128], lanes: usize) -> Vec<F128> {
        assert!(msg.len().is_multiple_of(lanes) && msg.len() / lanes <= self.size());
        let mut word = flock_prover::alloc_zeroed_vec::<F128>(self.size() * lanes);
        word[..msg.len()].copy_from_slice(msg);
        self.ntt.forward_transform_interleaved(&mut word, lanes);
        word
    }

    /// Encodes interleaved messages over GF(2^256), coordinate by coordinate.
    pub fn encode_f256(&self, msg: &[F256], lanes: usize) -> Vec<F256> {
        let (c0, c1): (Vec<F128>, Vec<F128>) =
            msg.par_iter().map(|v| (v.coordinates()[0], v.coordinates()[1])).unzip();
        let (w0, w1) = rayon::join(|| self.encode(&c0, lanes), || self.encode(&c1, lanes));
        w0.into_par_iter().zip(w1).map(|(a, b)| F256::new(a, b)).collect()
    }
}
