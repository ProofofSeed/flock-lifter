// SPDX-License-Identifier: LGPL-3.0-or-later

//! The contract's matrix discharge closes exactly the claims the native structured discharge
//! closes, on the toy block.

use flock_prover::{field::F128, zerocheck::multilinear::lagrange_weights_naive};
use pofseed_flock_lift_block::{program::Program, toy::Toy};
use pofseed_flock_lift_evm::{
    discharge::{Stream, deploy, pack_claim, run},
    evm::Evm,
    mirror::MatrixClaim,
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
}

fn claim(program: &Program, rng: &mut Rng) -> (MatrixClaim, F128) {
    let rest = program.geometry().k_log() - 6;
    let z = rng.f128();
    let skip = lagrange_weights_naive(6, z);
    let mut mc = MatrixClaim {
        alpha: rng.f128(),
        beta: rng.f128(),
        skip_weights: skip.clone(),
        x_inner_rest: (0..rest).map(|_| rng.f128()).collect(),
        r_inner_rest: (0..rest).map(|_| rng.f128()).collect(),
        z_partial: (0..64).map(|_| rng.f128()).collect(),
        running: F128::ZERO,
    };
    let comb = program.comb_partial(mc.alpha, mc.beta, &skip, &mc.x_inner_rest, &mc.r_inner_rest);
    mc.running = comb.iter().zip(&mc.z_partial).fold(F128::ZERO, |acc, (&c, &zp)| acc + c * zp);
    return (mc, z);
}

#[test]
fn contract_discharge_matches_the_native_one_on_the_toy_block() {
    let program = Program::new(&Toy);
    eprintln!(
        "toy block: k_log {}, {} explicit rows, {} Keccak-f sub-blocks",
        program.geometry().k_log(),
        program.explicit_rows(),
        program.geometry().keccak_subs()
    );
    let mut rng = Rng(0x5eed_1234_dead_beef);
    let stream = Stream::new(&program, 1 << 16);
    eprintln!("stream: {} bytes in {} segments, {} head words", stream.len(), stream.segments.len(), stream.head_words);
    let mut evm = Evm::new();
    let at = deploy(&mut evm, &program, &stream);
    let (a, za) = claim(&program, &mut rng);
    let (b, zb) = claim(&program, &mut rng);
    let mut claims = pack_claim(&a, za);
    claims.extend(pack_claim(&b, zb));
    let gas = run(&mut evm, at, &stream, &claims);
    assert!(gas.accepted, "the contract refused genuine claims");
    eprintln!("{gas:?}");
    let mut wrong = claims.clone();
    let words = claims.len() / 2;
    wrong[words + 3] ^= revm::primitives::U256::from(1);
    assert!(!run(&mut evm, at, &stream, &wrong).accepted, "a wrong running claim was accepted");
    let other = Stream::new(&program, 1 << 15);
    assert!(!run(&mut evm, at, &other, &claims).accepted, "a different stream cut was accepted");
}
