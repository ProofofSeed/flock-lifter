// SPDX-License-Identifier: LGPL-3.0-or-later

//! The structured part computed in resumable pieces agrees with it computed whole.

use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::evm::{Abi, Evm, artifact};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use revm::primitives::{U256, keccak256};

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

    fn vec(&mut self, n: usize) -> Vec<U256> {
        return (0..n).map(|_| self.f128()).collect();
    }
}

fn call(sig: &str, input: &[u8], cuts: Option<&[U256]>) -> Vec<u8> {
    let mut out = keccak256(sig.as_bytes())[..4].to_vec();
    let heads = if cuts.is_some() { 2 } else { 1 };
    out.extend_from_slice(&U256::from(32 * heads).to_be_bytes::<32>());
    if cuts.is_some() {
        out.extend_from_slice(&U256::from(32 * heads + input.len()).to_be_bytes::<32>());
    }
    out.extend_from_slice(input);
    if let Some(c) = cuts {
        out.extend_from_slice(&U256::from(c.len()).to_be_bytes::<32>());
        for x in c {
            out.extend_from_slice(&x.to_be_bytes::<32>());
        }
    }
    return out;
}

#[test]
fn pieces_match_the_whole_fold() {
    let (_, chain_code) = bip32_vector_1();
    let program = Program::new(&HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET));
    let g = program.geometry();
    let mut evm = Evm::new();
    let (probe, _) = evm.deploy(artifact("StructuredProbe.sol", "StructuredProbe"));
    let mut rng = Rng(0x1234_5678_9abc_def1);
    for cuts in [vec![], vec![5, 10, 15, 20], vec![1, 2, 23]] {
        let input = Abi::default()
            .uint(rng.f128())
            .uint(rng.f128())
            .uints(&rng.vec(64))
            .uints(&rng.vec(64))
            .uints(&rng.vec(22))
            .uints(&rng.vec(22))
            .uint(U256::from(g.head_subs()))
            .uint(U256::from(g.keccak_subs()))
            .finish(Vec::new());
        let cuts: Vec<U256> = cuts.into_iter().map(U256::from).collect();
        let sig = "(uint256,uint256,uint256[],uint256[],uint256[],uint256[],uint256,uint256)";
        let whole = evm.call(probe, call(&format!("whole({sig})"), &input, None));
        let pieces = evm.call(probe, call(&format!("pieces({sig},uint256[])"), &input, Some(&cuts)));
        assert!(whole.success && pieces.success);
        eprintln!("cuts {cuts:?}: whole {} gas, pieces {} gas", whole.gas, pieces.gas);
        assert_eq!(whole.output, pieces.output, "cuts {cuts:?}");
    }
}
