// SPDX-License-Identifier: LGPL-3.0-or-later

//! The shift extension against its definition, and the sumcheck engine on a product term.

use flock_prover::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    lincheck::build_eq_table,
};
use pofseed_flock_lift_structure::{
    adder::rotated_eq,
    sumcheck::{self, Term},
};

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

    fn vec(&mut self, n: usize) -> Vec<F128> {
        return (0..n).map(|_| self.f128()).collect();
    }
}

#[test]
fn the_shift_extension_matches_its_definition() {
    let mut rng = Rng(0x1111_2222_3333_4444);
    for n in [1usize, 3, 6] {
        let (x, y, b) = (rng.vec(n), rng.vec(n), rng.vec(n));
        let (ex, ey, eb) = (build_eq_table(&x), build_eq_table(&y), build_eq_table(&b));
        let size = 1usize << n;
        let mut expected = F128::ZERO;
        for t in 0..size {
            for u in 0..size {
                expected += ex[t] * ey[u] * eb[(t + u) % size];
            }
        }
        assert_eq!(rotated_eq(&x, &y, &b), expected, "{n} bits");
    }
}

struct Cubic(F128);

impl Term for Cubic {
    fn degree(&self) -> usize {
        return 4;
    }

    fn eval(&self, row: &[F128]) -> F128 {
        return row[0] * row[1] * row[2] * (self.0 + row[3]) + row[1] * row[1];
    }
}

fn mle(column: &[F128], point: &[F128]) -> F128 {
    return build_eq_table(point).iter().zip(column).fold(F128::ZERO, |acc, (&e, &v)| acc + e * v);
}

#[test]
fn the_engine_proves_a_sum_and_refuses_another() {
    let mut rng = Rng(0x5555_6666_7777_8888);
    let vars = 7;
    let term = Cubic(rng.f128());
    let columns: Vec<Vec<F128>> = (0..4).map(|_| rng.vec(1 << vars)).collect();
    let claim = (0..1usize << vars).fold(F128::ZERO, |acc, i| {
        let row: Vec<F128> = columns.iter().map(|c| c[i]).collect();
        acc + term.eval(&row)
    });
    let mut ch = FsChallenger::new(b"sumcheck-test");
    let (rounds, point, finals) = sumcheck::prove(&term, columns.clone(), claim, &mut ch);
    for (column, &v) in columns.iter().zip(&finals) {
        assert_eq!(mle(column, &point), v, "a column's extension at the point");
    }
    let mut ch = FsChallenger::new(b"sumcheck-test");
    let (last, replayed) = sumcheck::verify(4, vars, claim, &rounds, &mut ch).expect("an honest sumcheck replays");
    assert_eq!(replayed, point);
    assert_eq!(last, term.eval(&finals), "the final claim is the term at the point");
    let mut ch = FsChallenger::new(b"sumcheck-test");
    let (last, _) = sumcheck::verify(4, vars, claim + F128::ONE, &rounds, &mut ch).expect("shape");
    assert_ne!(last, term.eval(&finals), "another claim does not close");
    let mut tampered = rounds.clone();
    tampered.messages[2][1] += F128::ONE;
    let mut ch = FsChallenger::new(b"sumcheck-test");
    assert!(sumcheck::verify(4, vars, claim, &tampered, &mut ch).is_none_or(|(l, _)| l != term.eval(&finals)));
    let _ = ch.sample_f128();
}
