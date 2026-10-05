// SPDX-License-Identifier: LGPL-3.0-or-later
//! The encoding evaluates novel-basis coefficients at the points whose coordinates the domain reports.

use flock_prover::field::F128;
use pofseed_flock_lift_whir::domain::Domain;

fn sample(n: usize, seed: u64) -> Vec<F128> {
    let mut x = seed | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            F128::new(x, x.rotate_left(29))
        })
        .collect()
}

#[test]
fn codeword_is_the_novel_basis_polynomial_at_the_reported_coordinates() {
    for (log_size, n, lanes) in [(6, 4, 1), (8, 5, 4), (9, 6, 2)] {
        let domain = Domain::new(log_size);
        let msg = sample((1 << n) * lanes, log_size as u64);
        let word = domain.encode(&msg, lanes);
        for pos in 0..domain.size() {
            let w = domain.coordinates(pos, n);
            for lane in 0..lanes {
                let mut acc = F128::ZERO;
                for c in 0..1usize << n {
                    let basis =
                        (0..n).fold(F128::ONE, |p, i| if (c >> i) & 1 == 1 { p * w[i] } else { p });
                    acc += msg[c * lanes + lane] * basis;
                }
                assert_eq!(
                    word[pos * lanes + lane],
                    acc,
                    "domain 2^{log_size}, position {pos}, lane {lane}"
                );
            }
        }
    }
}
