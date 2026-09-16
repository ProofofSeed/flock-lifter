// SPDX-License-Identifier: LGPL-3.0-or-later

//! The contract's field arithmetic agrees with Flock's, and what it costs.

use flock_prover::{
    field::{F128, F256},
    lincheck::build_eq_table,
};
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
    let (probe, _) = evm.deploy(artifact("GF2Probe.sol", "GF2Probe"));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for i in 0..64 {
        let (a, b) = (rng.f128(), rng.f128());
        let (a, b) = if i == 0 { (F128::ZERO, b) } else if i == 1 { (F128::ONE, b) } else { (a, b) };
        let out = evm.call(probe, encode("mul(uint256,uint256)", |x| x.uint(u(a)).uint(u(b))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u(a * b), "mul");
        let out = evm.call(probe, encode("sq(uint256)", |x| x.uint(u(a))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u(a * a), "sq");
        let out = evm.call(probe, encode("inv(uint256)", |x| x.uint(u(a))));
        let expect = if a == F128::ZERO { F128::ZERO } else { a.inv() };
        assert_eq!(U256::from_be_bytes(out.word(0)), u(expect), "inv");
        let (c, d) = (F256::new(a, b), F256::new(rng.f128(), rng.f128()));
        let out = evm.call(probe, encode("mul256(uint256,uint256)", |x| x.uint(u256(c)).uint(u256(d))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u256(c * d), "mul256");
        let mut native = [0u8; 16];
        native[..8].copy_from_slice(&a.lo.to_le_bytes());
        native[8..].copy_from_slice(&a.hi.to_le_bytes());
        let out = evm.call(probe, encode("fromNative(uint256)", |x| x.u128(u128::from_be_bytes(native))));
        assert_eq!(U256::from_be_bytes(out.word(0)), u(a), "fromNative");
    }
    let point: Vec<F128> = (0..5).map(|_| rng.f128()).collect();
    let args: Vec<U256> = point.iter().map(|&p| u(p)).collect();
    let out = evm.call(probe, encode("eqTable(uint256[])", |x| x.uints(&args)));
    let table = build_eq_table(&point);
    for (i, &t) in table.iter().enumerate() {
        assert_eq!(U256::from_be_bytes(out.word(2 + i)), u(t), "eq table entry {i}");
    }
    let (a, b) = (rng.f128(), rng.f128());
    let out = evm.call(probe, encode("meter(uint256,uint256,uint256)", |x| x.uint(u(a)).uint(u(b)).uint(U256::from(1000))));
    let mul_gas = U256::from_be_bytes(out.word(0)).to::<u64>();
    let sq_gas = U256::from_be_bytes(out.word(1)).to::<u64>();
    eprintln!("gas per multiplication {:.1}, per squaring {:.1}", mul_gas as f64 / 1000.0, sq_gas as f64 / 1000.0);
}
