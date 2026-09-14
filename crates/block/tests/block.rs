// SPDX-License-Identifier: LGPL-3.0-or-later

//! Differential tests of the response block against ZKBoo's own view replay, and of the
//! structured lincheck fold against the witness it folds.

use flock_prover::{field::F128, lincheck::LincheckCircuit};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_statement::{H, HardenedChildCircuit, PS, PV, S};
use zkboo::{
    backend::{Backend, Frontend, WordRef},
    circuit::Circuit,
    executor::{ExecOptions, OwnedFlexibleWordPool, exec},
    prover::{par_prove, proof::Response, views::OwnedFlexibleWordTriplePool},
    verifier::replay::{OwnedFlexibleWordPairPool, ViewReplayerBackend},
    word::{Word, Words},
};

type WP = OwnedFlexibleWordPool<usize>;
type WTP = OwnedFlexibleWordTriplePool<usize>;
type WPP = OwnedFlexibleWordPairPool<usize>;

struct Toy;

impl Circuit for Toy {
    fn exec<B: Backend>(&self, frontend: &Frontend<B>) {
        let bytes: Vec<WordRef<B, u8>> = (0..32u8).map(|i| frontend.input(i.wrapping_mul(7) ^ 0x33)).collect();
        let a = bytes[0].clone().bitand(bytes[1].clone());
        let b = bytes[2].clone().not().bitxor_const(0x5au8);
        let c = a.wrapping_add(b);
        let d = c.rotate_left(3).unbounded_shr(1).unbounded_shl(2).reverse_bits();
        let x = bytes[3].clone().cast::<u64>().rotate_left(13) ^ bytes[4].clone().cast::<u64>().swap_bytes();
        let y = x.clone().wrapping_add(bytes[5].clone().cast::<u64>().bitand_const(0xF0F0u64));
        let z = x.bitand(y.clone()).bitxor_const(0x0123_4567_89ab_cdefu64);
        let comp = WordRef::<B, u64, 4>::from_le_words([
            y.clone(),
            z.clone(),
            y.clone().not(),
            z.clone().rotate_right(7),
        ]);
        let comp2 = comp
            .clone()
            .wrapping_add(comp.clone().rotate_left(70))
            .bitand(comp.swap_bytes())
            .reverse_bits()
            .unbounded_shr(9);
        let small = z.cast::<u32>();
        let s2 = small.clone().bitand(small.clone().rotate_left(5)).cast::<u8>();
        frontend.output(d);
        frontend.output(s2);
        frontend.output(small);
        frontend.output(comp2);
        frontend.output(y);
        frontend.output(bytes[31].clone());
    }
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

fn words_bits(words: &Words) -> Vec<bool> {
    fn push<W: Word>(words: &Words, bits: &mut Vec<bool>) {
        for &w in words.as_vec::<W>() {
            for b in 0..W::WIDTH {
                bits.push((w >> b) & W::ONE == W::ONE);
            }
        }
    }
    let mut bits = Vec::new();
    push::<u8>(words, &mut bits);
    push::<u32>(words, &mut bits);
    push::<u64>(words, &mut bits);
    return bits;
}

fn native_io<C: Circuit>(program: &Program, circuit: &C, output: &Words, response: &Response<S, S>) -> Vec<F128> {
    let frontend = ViewReplayerBackend::<H, PV, S, WPP>::new(response).into_view_replayer();
    circuit.exec(&frontend);
    let commitments = frontend.finalize_with_arg(output).expect("native replay");
    let c = response.challenge().index();
    let mut words = vec![F128::new(1 << c, 0)];
    for s in 0..2 {
        let d = commitments[(c + s) % 3].digest();
        for k in 0..2 {
            let lo = u64::from_le_bytes(d[16 * k..16 * k + 8].try_into().unwrap());
            let hi = u64::from_le_bytes(d[16 * k + 8..16 * k + 16].try_into().unwrap());
            words.push(F128::new(lo, hi));
        }
    }
    for s in 0..2 {
        let bits = words_bits(commitments[(c + s) % 3].output_share());
        let mut packed = vec![0u64; 2 * program.geometry().out_words()];
        for (p, &bit) in bits.iter().enumerate() {
            packed[p / 64] |= (bit as u64) << (p % 64);
        }
        words.extend(packed.chunks(2).map(|w| F128::new(w[0], w[1])));
    }
    return words;
}

fn check<C: Circuit + Sync>(circuit: &C, witness_circuit: &C, responses: usize, fold_checks: usize) {
    let program = Program::new(circuit);
    let g = program.geometry();
    println!(
        "k_log {}, head {} bits ({} used), {} Keccak-f, {} products, {} materialised, {} explicit rows, nnz {:?}",
        g.k_log(),
        g.head_bits(),
        g.replay_base(),
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
        assert_eq!(program.io_words(&z), native_io(&program, circuit, &output, response), "published words, challenge {c}");
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

#[test]
fn toy_block_agrees_with_native_replay() {
    check(&Toy, &Toy, 24, 3);
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
    check(&public, &witness, 24, 1);
}
