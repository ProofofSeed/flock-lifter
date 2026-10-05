// SPDX-License-Identifier: LGPL-3.0-or-later

//! The wrap verifier's field arithmetic agrees with Flock's, and what it costs.

use flock_prover::field::{F128, F256};
use pofseed_flock_lift_evm::evm::{Evm, artifact, encode};
use revm::primitives::U256;

fn u(v: F128) -> U256 {
    return U256::from(((v.hi as u128) << 64) | v.lo as u128);
}

fn u256(v: F256) -> U256 {
    return (u(v.c1) << 128) | u(v.c0);
}

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
fn field_operations_agree_with_flock() {
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("FProbe.sol", "FProbe"));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let ones = F128::new(u64::MAX, u64::MAX);
    for i in 0..256 {
        let (a, b) = match i {
            0 => (F128::ZERO, rng.f128()),
            1 => (F128::ONE, rng.f128()),
            2 => (ones, ones),
            3 => (ones, rng.f128()),
            4 => (F128::new(0, 1 << 63), F128::new(0, 1 << 63)),
            _ => (rng.f128(), rng.f128()),
        };
        let out = evm.call(probe, encode("mul(uint256,uint256)", |x| x.uint(u(a)).uint(u(b))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u(a * b), "mul");
        let out = evm.call(probe, encode("sq(uint256)", |x| x.uint(u(a))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u(a * a), "sq");
        let (c, d) = (F256::new(a, b), F256::new(rng.f128(), rng.f128()));
        let out = evm.call(probe, encode("mul256(uint256,uint256)", |x| x.uint(u256(c)).uint(u256(d))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u256(c * d), "mul256");
    }
    let (a, b) = (rng.f128(), rng.f128());
    let out = evm.call(probe, encode("meter(uint256,uint256,uint256)", |x| x.uint(u(a)).uint(u(b)).uint(U256::from(1000))));
    let gas = |i: usize| U256::from_be_bytes(out.word(i)).to::<u64>() as f64 / 1000.0;
    eprintln!("gas per multiplication {:.1}, per squaring {:.1}, per extension multiplication {:.1}", gas(0), gas(1), gas(2));
}

#[test]
fn kernels_agree_with_the_library() {
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("KProbe.sol", "KProbe"));
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let n = 512;
    let a: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
    let b: Vec<F128> = (0..n).map(|_| rng.f128()).collect();
    let (ua, ub): (Vec<U256>, Vec<U256>) = (a.iter().map(|&v| u(v)).collect(), b.iter().map(|&v| u(v)).collect());
    let out = evm.call(probe, encode("dot(uint256[],uint256[])", |x| x.uints(&ua).uints(&ub)));
    let expect = a.iter().zip(&b).fold(F128::ZERO, |acc, (&x, &y)| acc + x * y);
    assert_eq!(U256::from_be_bytes(out.word(0)), u(expect), "dot kernel");
    assert_eq!(U256::from_be_bytes(out.word(1)), u(expect), "dot library");
    eprintln!("gas per term of a dot product: {:.1}", U256::from_be_bytes(out.word(2)).to::<u64>() as f64 / n as f64);
    let point: Vec<F128> = (0..9).map(|_| rng.f128()).collect();
    let args: Vec<U256> = point.iter().map(|&p| u(p)).collect();
    let out = evm.call(probe, encode("eqTable(uint256[])", |x| x.uints(&args)));
    let table = flock_prover::lincheck::build_eq_table(&point);
    for (i, &t) in table.iter().enumerate() {
        assert_eq!(U256::from_be_bytes(out.word(3 + i)), u(t), "eq table entry {i}");
    }
    eprintln!("gas per entry of an equality table: {:.1}", U256::from_be_bytes(out.word(1)).to::<u64>() as f64 / 512.0);
    for _ in 0..32 {
        let (c, d) = (F256::new(rng.f128(), rng.f128()), F256::new(rng.f128(), rng.f128()));
        let out = evm.call(probe, encode("mul256(uint256,uint256,uint256)", |x| x.uint(u256(c)).uint(u256(d)).uint(U256::from(100))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u256(c * d), "mul256 kernel");
        assert_eq!(U256::from_be_bytes(out.word(1)), u256(c * d), "mul256 library");
        if c.c0.lo & 31 == 0 {
            eprintln!("gas per extension multiplication: {:.1}", U256::from_be_bytes(out.word(2)).to::<u64>() as f64 / 100.0);
        }
    }
    let v = rng.f128();
    let out = evm.call(probe, encode("frob(uint256,uint256)", |x| x.uint(u(v)).uint(U256::from(127))));
    assert_eq!(out.word(0), out.word(1), "frob");
    eprintln!("gas per squaring: {:.1}", U256::from_be_bytes(out.word(2)).to::<u64>() as f64 / 127.0);
    let out = evm.call(probe, encode("products(uint256)", |x| x.uint(U256::from(23))));
    eprintln!(
        "gas per factor of an equality product over the extension {:.1}, of a shift product {:.1}",
        U256::from_be_bytes(out.word(0)).to::<u64>() as f64 / 23.0,
        U256::from_be_bytes(out.word(1)).to::<u64>() as f64 / 23.0
    );
}
