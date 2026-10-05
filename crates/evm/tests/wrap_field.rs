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
