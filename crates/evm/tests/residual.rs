// SPDX-License-Identifier: LGPL-3.0-or-later

//! The assembly residual evaluations agree with the table-per-point ones they replaced, on random
//! inputs covering every path, and what each costs.

use pofseed_flock_lift_evm::evm::{Evm, artifact, encode};
use revm::primitives::U256;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        return self.0;
    }

    fn f128(&mut self) -> U256 {
        return U256::from(((self.next() as u128) << 64) | self.next() as u128);
    }

    fn f256(&mut self) -> U256 {
        return (self.f128() << 128) | self.f128();
    }
}

fn pair(out: &pofseed_flock_lift_evm::evm::Outcome) -> (U256, u64) {
    assert!(out.success, "probe reverted: {}", hex::encode(&out.output));
    return (U256::from_be_bytes(out.word(0)), U256::from_be_bytes(out.word(1)).to::<u64>());
}

#[test]
fn consistency_matches_the_per_query_evaluation() {
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("ResidualProbe.sol", "ResidualProbe"));
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for (f, ext, rate, count) in [(0, 4, 1, 23), (3, 4, 1, 8), (12, 5, 1, 244), (18, 4, 1, 244), (15, 4, 3, 79), (6, 5, 5, 48), (9, 4, 7, 35)] {
        let log_cols = f + ext;
        let d = log_cols + rate;
        let bits = (usize::BITS - (count as usize - 1).leading_zeros()) as usize;
        let qs: Vec<U256> = (0..count).map(|_| U256::from(rng.next() & ((1u64 << d) - 1))).collect();
        let alpha: Vec<U256> = (0..bits).map(|_| rng.f128()).collect();
        let fixed: Vec<U256> = (0..f).map(|_| rng.f256()).collect();
        let mu: Vec<U256> = (0..1usize << ext).map(|_| rng.f256()).collect();
        let args = |sig: &str| {
            encode(sig, |a| a.uint(U256::from(log_cols)).uints(&qs).uints(&alpha).uints(&fixed).uints(&mu))
        };
        let (new, new_gas) = pair(&evm.call(probe, args("consistency(uint256,uint256[],uint256[],uint256[],uint256[])")));
        let (old, old_gas) = pair(&evm.call(probe, args("consistencyOld(uint256,uint256[],uint256[],uint256[],uint256[])")));
        eprintln!("consistency f={f} ext={ext} rate={rate} queries={count}: {old_gas} -> {new_gas} gas");
        assert_eq!(new, old, "f={f} ext={ext} rate={rate} queries={count}");
    }
}

#[test]
fn ring_switch_matches_the_table_per_point_evaluation() {
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("ResidualProbe.sol", "ResidualProbe"));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for (p_len, ext, claims, binary) in [(3, 2, 1, 0), (16, 5, 1, 0), (24, 4, 3, 17), (8, 3, 2, 8), (0, 2, 1, 0), (6, 3, 2, 2)] {
        let ris: Vec<U256> = (0..p_len).map(|_| rng.f256()).collect();
        let mut flat_x = Vec::new();
        for c in 0..claims {
            flat_x.push(rng.f128());
            for i in 0..p_len + ext {
                let z = if c + 1 == claims && i >= 4 && i < 4 + binary { U256::from(rng.next() & 1) } else { rng.f128() };
                flat_x.push(z);
            }
        }
        let flat_eq: Vec<U256> = (0..128 * claims).map(|_| rng.f128()).collect();
        let gammas: Vec<U256> = (0..claims).map(|_| rng.f128()).collect();
        let mu: Vec<U256> = (0..1usize << ext).map(|_| rng.f256()).collect();
        let args = |sig: &str| encode(sig, |a| a.uints(&ris).uints(&flat_x).uints(&flat_eq).uints(&gammas).uints(&mu));
        let (new, new_gas) = pair(&evm.call(probe, args("ringSwitch(uint256[],uint256[],uint256[],uint256[],uint256[])")));
        let (old, old_gas) = pair(&evm.call(probe, args("ringSwitchOld(uint256[],uint256[],uint256[],uint256[],uint256[])")));
        eprintln!("ring switch prefix={p_len} ext={ext} claims={claims} binary={binary}: {old_gas} -> {new_gas} gas");
        assert_eq!(new, old, "prefix={p_len} ext={ext} claims={claims} binary={binary}");
    }
}
