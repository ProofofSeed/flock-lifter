// SPDX-License-Identifier: LGPL-3.0-or-later

//! Bits of committed bytes from the bytes' extension at conjugate points.

use flock_prover::{field::F128, lincheck::build_eq_table};
use pofseed_flock_lift_structure::subfield::{are_conjugates, bit_value, bits, conjugates, embed};

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

#[test]
fn bit_extensions_come_from_the_bytes_at_conjugates() {
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    let vars = 9;
    let table: Vec<u8> = (0..1 << vars).map(|_| rng.next() as u8).collect();
    let point: Vec<F128> = (0..vars).map(|_| rng.f128()).collect();
    let conj = conjugates(&point);
    assert!(are_conjugates(&conj));
    let at: Vec<F128> = conj
        .iter()
        .map(|p| build_eq_table(p).iter().zip(&table).fold(F128::ZERO, |acc, (&e, &v)| acc + e * embed(v)))
        .collect();
    let eq = build_eq_table(&point);
    let direct: Vec<F128> = (0..8)
        .map(|i| eq.iter().zip(&table).fold(F128::ZERO, |acc, (&e, &v)| if v >> i & 1 == 1 { acc + e } else { acc }))
        .collect();
    assert_eq!(bits(&at).to_vec(), direct);
    let low: Vec<F128> = (0..3).map(|_| rng.f128()).collect();
    let weights = build_eq_table(&low);
    let expected = direct.iter().zip(&weights).fold(F128::ZERO, |acc, (&b, &w)| acc + b * w);
    assert_eq!(bit_value(&low, &at), expected);
    let mut wrong = conj.clone();
    wrong[3][2] += F128::ONE;
    assert!(!are_conjugates(&wrong));
}
