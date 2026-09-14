// SPDX-License-Identifier: LGPL-3.0-or-later

//! Proves and verifies a toy Boolean table through Flock's circuit path, with a hand-packed
//! witness, a hand-built lincheck stripe and published output words.

use std::time::Instant;

use flock_prover::{
    challenger::FsChallenger,
    circuit::builder::{CircuitBuilder, GateType, SlotWitness},
    field::F128,
    lincheck::SparseMatrixCircuit,
    pcs::{
        PcsParams,
        ligerito::{LigeritoProfile, embedded_initial_k_or_default},
    },
    prover::{UnionSlotProverInput, prove_fast_ligerito_union_circuit},
    r1cs::SparseBinaryMatrix,
    schedule::{IoWord, TableType},
    union::UnionInstance,
    verifier::verify_ligerito_union_circuit,
};

const K_LOG: usize = 16;
const K: usize = 1 << K_LOG;
const NU: usize = 6;
const CONST: usize = 0;
const OUT: usize = 128;
const X: usize = 512;
const P: usize = 1024;
const W: usize = 256;
const DOMAIN: &[u8] = b"pofseed-flock-spike-v0";

struct ToyGate;

fn matrices() -> (SparseBinaryMatrix, SparseBinaryMatrix) {
    let mut a = vec![Vec::new(); K];
    let mut b = vec![Vec::new(); K];
    a[CONST] = vec![CONST];
    b[CONST] = vec![CONST];
    for i in 0..W {
        a[X + i] = vec![X + i];
        b[X + i] = vec![CONST];
        a[P + i] = vec![X + i];
        b[P + i] = vec![CONST, X + (i + 1) % W];
        a[OUT + i] = vec![CONST, P + i, X + (i + 2) % W];
        a[OUT + i].sort();
        b[OUT + i] = vec![CONST];
    }
    return (SparseBinaryMatrix::new(K, K, a), SparseBinaryMatrix::new(K, K, b));
}

fn bit(words: &[u64], i: usize) -> bool {
    return (words[i / 64] >> (i % 64)) & 1 == 1;
}

fn set(words: &mut [u64], i: usize, v: bool) {
    if v {
        words[i / 64] |= 1 << (i % 64);
    }
}

fn instance_witness(x: &[u64; 4], flip: Option<usize>) -> [Vec<u64>; 3] {
    let mut z = vec![0u64; K / 64];
    let mut za = vec![0u64; K / 64];
    let mut zb = vec![0u64; K / 64];
    set(&mut z, CONST, true);
    set(&mut za, CONST, true);
    set(&mut zb, CONST, true);
    for i in 0..W {
        let xi = bit(x, i);
        set(&mut z, X + i, xi);
        set(&mut za, X + i, xi);
        set(&mut zb, X + i, true);
        let nx = !bit(x, (i + 1) % W);
        set(&mut z, P + i, xi & nx);
        set(&mut za, P + i, xi);
        set(&mut zb, P + i, nx);
        let o = !((xi & nx) ^ bit(x, (i + 2) % W));
        set(&mut z, OUT + i, o ^ (flip == Some(i)));
        set(&mut za, OUT + i, o);
        set(&mut zb, OUT + i, true);
    }
    return [z, za, zb];
}

fn out_words(z: &[u64]) -> [F128; 2] {
    let w = OUT / 64;
    return [F128::new(z[w], z[w + 1]), F128::new(z[w + 2], z[w + 3])];
}

impl GateType for ToyGate {
    type Row = [u64; 4];
    type Hint = ([u64; 4], Option<usize>);

    fn table(&self) -> TableType {
        let (a_0, b_0) = matrices();
        let c_0 = SparseBinaryMatrix::new(K, K, (0..K).map(|i| vec![i]).collect());
        return TableType {
            k_log: K_LOG,
            useful_bits: K,
            a_0,
            b_0,
            c_0,
            const_pin: Some(CONST),
            class: Default::default(),
            io_schema: vec![IoWord::output(OUT / 128), IoWord::output(OUT / 128 + 1)],
        };
    }

    fn eval(&self, _inputs: &[F128], hint: &Self::Hint, outputs: &mut Vec<F128>) -> Self::Row {
        let [z, _, _] = instance_witness(&hint.0, hint.1);
        outputs.extend_from_slice(&out_words(&z));
        return hint.0;
    }

    fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
        return SlotWitness::DeferredToRows;
    }
}

fn pack(instances: &[[Vec<u64>; 3]]) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
    let n_total = 1usize << NU;
    let cols = K / 128;
    let mut bufs = [(); 3].map(|_| vec![F128::ZERO; cols << NU]);
    for (j, inst) in instances.iter().enumerate() {
        for (buf, words) in bufs.iter_mut().zip(inst.iter()) {
            for c in 0..cols {
                buf[(c << NU) + j] = F128::new(words[2 * c], words[2 * c + 1]);
            }
        }
    }
    let mut stripe = vec![0u8; (n_total / 8) * K];
    for (j, inst) in instances.iter().enumerate() {
        for i in 0..K {
            if bit(&inst[0], i) {
                stripe[(j / 8) * K + i] |= 1 << (j % 8);
            }
        }
    }
    let [z, a, b] = bufs;
    return (z, a, b, stripe);
}

fn run(flip: Option<usize>, tamper_public: bool) -> bool {
    let xs: Vec<[u64; 4]> = (0..8u64)
        .map(|j| [0x9e37_79b9_7f4a_7c15u64.wrapping_mul(j + 1), j ^ 0xdead_beef, !j, j << 7])
        .collect();
    let mut builder = CircuitBuilder::new(NU);
    let slot = builder.slot(ToyGate);
    for (j, x) in xs.iter().enumerate() {
        let outs = builder.gate_with_hint(slot, &[], (*x, if j == 5 { flip } else { None }));
        builder.publish(outs[0]);
        builder.publish(outs[1]);
    }
    let built = builder.finish().expect("valid circuit");
    let instances: Vec<[Vec<u64>; 3]> = xs
        .iter()
        .enumerate()
        .map(|(j, x)| instance_witness(x, if j == 5 { flip } else { None }))
        .collect();
    let witness = pack(&instances);
    let registry = &built.shape.registry;
    let ty = &registry.types()[0];
    let lc = SparseMatrixCircuit::new(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin);
    let mut union = UnionInstance::new(registry, built.shape.counts.clone());
    if union.dense_m() < 22 {
        union.set_dense_floor(22);
    }
    let m = union.dense_m();
    let profile = LigeritoProfile::Fast;
    let log_batch_size = embedded_initial_k_or_default(m, profile);
    let pcs_params = PcsParams {
        m,
        log_inv_rate: profile.log_inv_rate(),
        log_batch_size,
        profile,
        num_lanes: union.commit_lanes(log_batch_size),
        merkle_hash: Default::default(),
    };
    let t = Instant::now();
    let mut ch = FsChallenger::new(DOMAIN);
    let (proof, commitment, _) = prove_fast_ligerito_union_circuit(
        &union,
        &built.shape.circuit,
        &built.witness.public,
        &pcs_params,
        vec![UnionSlotProverInput::new(witness, &lc)],
        Vec::new(),
        &mut ch,
    );
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    let mut public = built.witness.public.clone();
    if tamper_public {
        public[3] += F128::ONE;
    }
    let t = Instant::now();
    let mut ch = FsChallenger::new(DOMAIN);
    let res = verify_ligerito_union_circuit(
        &union,
        &built.shape.circuit,
        &public,
        &[&lc],
        &commitment,
        &proof,
        &pcs_params,
        &mut ch,
    );
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;
    let size = bincode::serialize(&proof).unwrap().len() + bincode::serialize(&commitment).unwrap().len();
    println!(
        "m={m} flip={flip:?} tamper_public={tamper_public}: prove {prove_ms:.0} ms, verify {verify_ms:.1} ms, proof {size} B, result {:?}",
        res.as_ref().map(|_| ())
    );
    return res.is_ok();
}

fn main() {
    assert!(run(None, false), "honest proof must verify");
    assert!(!run(None, true), "tampered public output must be refused");
    assert!(!run(Some(17), false), "unsatisfying witness must be refused");
    println!("spike: all three cases behaved");
}
