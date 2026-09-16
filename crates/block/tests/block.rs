// SPDX-License-Identifier: LGPL-3.0-or-later

//! Differential tests of the response block against ZKBoo's own view replay, and of the
//! structured lincheck fold against the witness it folds.

use flock_prover::{
    field::F128,
    lincheck::{LincheckCircuit, build_quirky_eq_table_from_weights},
};
use pofseed_flock_lift_block::{native, program::Program, toy::Toy};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit, PS, PV, S};
use zkboo::{
    circuit::Circuit,
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, views::OwnedFlexibleWordTriplePool},
};

type WP = OwnedFlexibleWordPool<usize>;
type WTP = OwnedFlexibleWordTriplePool<usize>;

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

fn check<C: Circuit + Sync>(build: fn(&C) -> Program, circuit: &C, witness_circuit: &C, responses: usize, fold_checks: usize) {
    let program = build(circuit);
    let g = program.geometry();
    println!(
        "k_log {}, head {} bits, {} Keccak-f, {} products, {} materialised, {} explicit rows, nnz {:?}",
        g.k_log(),
        g.head_bits(),
        g.keccak_subs(),
        program.replay_products(),
        program.replay_materialised(),
        program.explicit_rows(),
        program.explicit_nnz()
    );
    let output = exec::<_, WP, _>(witness_circuit, ExecOptions::new());
    let proof = par_prove::<_, H, PS, PV, S, WTP>(witness_circuit, responses, b"block-test", b"binding");
    let mut seen = [false; 3];
    let mut folds = 0;
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for response in &proof {
        let c = response.challenge().index();
        if seen[c] {
            continue;
        }
        seen[c] = true;
        let words = program.block_bits() / 64;
        let (mut z, mut a, mut b) = (vec![0u64; words], vec![0u64; words], vec![0u64; words]);
        program.write_witness(response, &mut z, &mut a, &mut b).expect("witness");
        let expected = native::io_words(&program, circuit, &output, response).expect("native replay");
        assert_eq!(program.io_words(&z), expected, "published words, challenge {c}");
        for w in 0..words {
            assert_eq!(z[w], a[w] & b[w], "z = a·b at word {w}");
        }
        if folds < fold_checks {
            folds += 1;
            let alpha = rng.f128();
            let eq: Vec<F128> = (0..program.block_bits()).map(|_| rng.f128()).collect();
            let comb = program.fold_alpha_batched(alpha, &eq);
            let mut lhs = F128::ZERO;
            let mut rhs = F128::ZERO;
            for i in 0..program.block_bits() {
                let bit = |v: &[u64]| (v[i / 64] >> (i % 64)) & 1 == 1;
                if bit(&a) {
                    lhs += alpha * eq[i];
                }
                if bit(&b) {
                    lhs += eq[i];
                }
                if bit(&z) {
                    rhs += comb[i];
                }
            }
            assert_eq!(lhs, rhs, "fold identity, challenge {c}");
        }
    }
    assert_eq!(seen, [true; 3], "every challenge was exercised");
}

/// The dense route the structured discharge replaces: fold the matrices at every column, pin the
/// constant wire, then bind the top variable one round at a time down to `2^k_skip` entries.
fn dense_comb_partial(
    program: &Program,
    alpha: F128,
    beta: F128,
    skip_weights: &[F128],
    x_inner_rest: &[F128],
    r_inner_rest: &[F128],
) -> Vec<F128> {
    let eq_inner = build_quirky_eq_table_from_weights(skip_weights, x_inner_rest);
    let mut comb = program.fold_alpha_batched(alpha, &eq_inner);
    comb[0] += beta;
    for &r in r_inner_rest.iter().rev() {
        let half = comb.len() / 2;
        for i in 0..half {
            comb[i] = comb[i] + r * (comb[i + half] + comb[i]);
        }
        comb.truncate(half);
    }
    return comb;
}

fn check_discharge<C: Circuit>(build: fn(&C) -> Program, circuit: &C, k_skip: usize, rounds: usize) {
    let program = build(circuit);
    let mut rng = Rng(0xf0e1_d2c3_b4a5_9687);
    for _ in 0..rounds {
        let alpha = rng.f128();
        let beta = rng.f128();
        let skip: Vec<F128> = (0..1 << k_skip).map(|_| rng.f128()).collect();
        let rest = program.geometry().k_log() - k_skip;
        let x: Vec<F128> = (0..rest).map(|_| rng.f128()).collect();
        let r: Vec<F128> = (0..rest).map(|_| rng.f128()).collect();
        let structured = program.comb_partial(alpha, beta, &skip, &x, &r);
        assert_eq!(structured, dense_comb_partial(&program, alpha, beta, &skip, &x, &r));
        assert!(structured.iter().any(|&v| v != F128::ZERO), "the discharge is not trivially zero");
    }
}

#[test]
fn toy_block_agrees_with_native_replay() {
    check(Program::new, &Toy, &Toy, 24, 3);
}

#[test]
fn toy_uniform_block_agrees_with_native_replay() {
    check(Program::uniform, &Toy, &Toy, 24, 3);
}

#[test]
fn toy_structured_discharge_matches_the_dense_fold() {
    check_discharge(Program::new, &Toy, 6, 4);
}

#[test]
fn toy_uniform_structured_discharge_matches_the_dense_fold() {
    check_discharge(Program::uniform, &Toy, 6, 4);
}

#[test]
#[ignore]
fn hardened_child_structured_discharge_matches_the_dense_fold() {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    check_discharge(Program::new, &HardenedChildCircuit::public_only(chain_code, 0x8000_0000), 6, 1);
}

#[test]
#[ignore]
fn hardened_child_uniform_structured_discharge_matches_the_dense_fold() {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    check_discharge(Program::uniform, &HardenedChildCircuit::public_only(chain_code, 0x8000_0000), 6, 1);
}

#[test]
#[ignore]
fn hardened_child_block_agrees_with_native_replay() {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let parent_priv = hex("e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35");
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    let index = 0x8000_0000;
    let witness = HardenedChildCircuit::with_witness(chain_code.clone(), parent_priv, index);
    let public = HardenedChildCircuit::public_only(chain_code, index);
    check(Program::new, &public, &witness, 24, 1);
}

#[test]
#[ignore]
fn hardened_child_uniform_block_agrees_with_native_replay() {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let parent_priv = hex("e8f32e723decf4051aefac8e2c93c9c5b214313817cdb01a1494b917c8436b35");
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    let index = 0x8000_0000;
    let witness = HardenedChildCircuit::with_witness(chain_code.clone(), parent_priv, index);
    let public = HardenedChildCircuit::public_only(chain_code, index);
    check(Program::uniform, &public, &witness, 24, 1);
}
