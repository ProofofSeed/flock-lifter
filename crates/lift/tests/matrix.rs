// SPDX-License-Identifier: LGPL-3.0-or-later

//! The committed-matrix proof: acceptance of genuine claims, and refusal of each kind of forgery.

use std::time::Instant;

use flock_prover::{challenger::Challenger, field::F128};
use pofseed_flock_lift::{
    matrix::{ExplicitClaim, MatrixError, MatrixKey, MatrixProof, prove, verify},
    transcript::KeccakChallenger,
};
use pofseed_flock_lift_block::{
    committed::{entries, value},
    program::Program,
    toy::Toy,
};
use pofseed_flock_lift_statement::HardenedChildCircuit;

const DOMAIN: &[u8] = b"matrix-test";

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

fn claims(program: &Program, list: &[u64], count: usize, rng: &mut Rng) -> Vec<ExplicitClaim> {
    let rest = program.geometry().k_log() - 6;
    return (0..count)
        .map(|_| {
            let mut c = ExplicitClaim {
                alpha: rng.f128(),
                skip: rng.vec(64),
                z: rng.vec(64),
                x: rng.vec(rest),
                r: rng.vec(rest),
                value: F128::ZERO,
            };
            c.value = value(list, &c.tables());
            c
        })
        .collect();
}

fn check(key: &MatrixKey, claims: &[ExplicitClaim], proof: &MatrixProof) -> Result<(), MatrixError> {
    return verify(&key.verifying(), claims, proof, &mut KeccakChallenger::new(DOMAIN));
}

#[test]
fn toy_matrix_proof_accepts_and_refuses_forgeries() {
    let program = Program::new(&Toy);
    let list = entries(&program);
    let key = MatrixKey::new(list.clone());
    let mut rng = Rng(0x1357_9bdf_2468_ace0);
    let cs = claims(&program, &list, 2, &mut rng);
    let proof = prove(&key, &cs, &mut KeccakChallenger::new(DOMAIN));
    assert_eq!(check(&key, &cs, &proof), Ok(()));

    let mut wrong = cs.clone();
    wrong[1].value += F128::ONE;
    let forged = prove(&key, &wrong, &mut KeccakChallenger::new(DOMAIN));
    assert_eq!(check(&key, &wrong, &forged), Err(MatrixError::Main), "a wrong value");
    assert!(check(&key, &wrong, &proof).is_err(), "a proof for other claims");

    let mut p = proof.clone();
    p.counts[300] += F128::ONE;
    assert_eq!(check(&key, &cs, &p), Err(MatrixError::Main), "a tampered count");
    let mut p = proof.clone();
    p.bits[50] += F128::ONE;
    assert_eq!(check(&key, &cs, &p), Err(MatrixError::Count), "a tampered address bit");
    let mut p = proof.clone();
    p.main[3].0[2] += F128::ONE;
    assert!(check(&key, &cs, &p).is_err(), "a tampered main round");
    let mut p = proof.clone();
    p.count[1].0[0] += F128::ONE;
    assert!(check(&key, &cs, &p).is_err(), "a tampered count round");
    let mut p = proof.clone();
    p.zeta_nonce ^= 1;
    assert!(check(&key, &cs, &p).is_err(), "a tampered nonce");

    let mut other = list.clone();
    other[7] ^= 1 << 45;
    let other_key = MatrixKey::new(other);
    assert!(
        verify(&other_key.verifying(), &cs, &proof, &mut KeccakChallenger::new(DOMAIN)).is_err(),
        "another statement's commitment"
    );
    let mut ch = KeccakChallenger::new(DOMAIN);
    ch.observe_label(b"elsewhere");
    assert!(verify(&key.verifying(), &cs, &proof, &mut ch).is_err(), "another transcript");
}

#[test]
#[ignore]
fn hardened_child_matrix_proof() {
    let hex = |s: &str| (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect::<Vec<u8>>();
    let chain_code = hex("873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508");
    let program = Program::new(&HardenedChildCircuit::public_only(chain_code, 0x8000_0000));
    let t = Instant::now();
    let list = entries(&program);
    let key = MatrixKey::new(list.clone());
    println!("{} entries, key built in {:.2} s", list.len(), t.elapsed().as_secs_f64());
    let mut rng = Rng(0x0f1e_2d3c_4b5a_6978);
    let cs = claims(&program, &list, 2, &mut rng);
    let t = Instant::now();
    let proof = prove(&key, &cs, &mut KeccakChallenger::new(DOMAIN));
    println!(
        "proved in {:.2} s, {} bytes",
        t.elapsed().as_secs_f64(),
        bincode::serialize(&proof).unwrap().len()
    );
    let t = Instant::now();
    assert_eq!(check(&key, &cs, &proof), Ok(()));
    println!("verified in {:.3} s", t.elapsed().as_secs_f64());
    let mut wrong = cs.clone();
    wrong[0].value += F128::ONE;
    assert!(check(&key, &wrong, &proof).is_err());
}

#[cfg(feature = "forgery")]
#[test]
fn toy_forged_proofs_are_refused_by_the_check_they_target() {
    use pofseed_flock_lift::matrix::{Forge, prove_forged};
    let program = Program::new(&Toy);
    let list = entries(&program);
    let key = MatrixKey::new(list.clone());
    let mut rng = Rng(0x7777_1111_3333_5555);
    let mut cs = claims(&program, &list, 2, &mut rng);
    cs[0].value += F128::ONE;
    let counts = prove_forged(&key, &cs, Forge::Counts, &mut KeccakChallenger::new(DOMAIN));
    assert_eq!(check(&key, &cs, &counts), Err(MatrixError::Count), "forged counts pass the main sumcheck");
    let bits = prove_forged(&key, &cs, Forge::Bits, &mut KeccakChallenger::new(DOMAIN));
    assert_eq!(check(&key, &cs, &bits), Err(MatrixError::Opening), "forged bits pass the count sumcheck");
}
