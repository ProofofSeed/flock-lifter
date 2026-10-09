// SPDX-License-Identifier: LGPL-3.0-or-later

//! Lifts a hardened-child proof through the wrap and checks the contract's mirror against the
//! lifter's own verifier.
//!
//! Usage: `wrap-check [responses] [chunk] [log inverse rate]` (default 8, 4, 1).

use std::{env, sync::Arc, time::Instant};

use pofseed_flock_lift::{lift::Statement, root, wrapped};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    mirror::Reader,
    wrap::{encode, opening, outer, vk::Vk},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
};

fn main() {
    let arg = |i: usize, d: usize| env::args().nth(i).map(|a| a.parse().expect("a number")).unwrap_or(d);
    let (n, chunk, rate) = (arg(1, 8), arg(2, 4), arg(3, 1));
    let whir = WhirOuter::new(4, rate, Regime::Johnson, 3, 22, 128).with_merkle(MerkleHash::Keccak);
    let (_, chain_code) = bip32_vector_1();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    let binding = b"flock-lifter wrap check binding";
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter wrap check entropy", binding);
    let statement = Statement {
        chain_code,
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: binding.to_vec(),
    };
    let t = Instant::now();
    let (key, lifted, _) = wrapped::prove(&program, &statement, &proof, chunk, &whir, None, rate).expect("a lift");
    println!("lifted {n} responses in {:.1} s", t.elapsed().as_secs_f64());
    wrapped::verify(&program, &key, &statement, &lifted, &whir).expect("the lift verifies");
    let words = wrapped::words(&program, &key, &lifted).expect("published words");
    let y = &statement.expected_output;
    let counts = (y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32)) as u64;
    let vk = Vk::new(&key, whir.config(key.wrap.key.pcs.m - 7), words[0].len(), counts);
    let (claims, mut native_tr) =
        root::outer_claims(&key.wrap, &key.root.table_of, &lifted.wrap, Some(&whir)).expect("the outer proof verifies");
    let (data, _opening) = encode::encode_outer(&vk, &lifted.wrap, claims.cells.1[0], claims.cells.1[1]);
    println!("outer calldata before the opening: {} B", data.len());
    let mut rd = Reader::new(&data);
    let public = outer::read_public(&vk, &mut rd, &words).expect("public words");
    assert_eq!(public, lifted.wrap.public, "the public segment");
    let (p, mut tr, _cap) = outer::piops(&vk, &mut rd, &public).expect("the mirror accepts the interactive proofs");
    assert_eq!(p.claims.block, claims.block, "block claims");
    assert_eq!(p.claims.tables, claims.tables, "table claims");
    assert_eq!(p.claims.cells, claims.cells, "cell claims");
    println!("interactive proofs: the mirror's claims are the lifter's ✓");
    {
        use flock_prover::{field::F128, pcs::ring_switch::{build_fold_byte_table, linearized_coefficients}, lincheck::build_eq_table};
        let r: Vec<F128> = (1..8u64).map(|i| F128::new(i * 0x9E37_79B9_7F4A_7C15, i.wrapping_mul(0xD1B5_4A32_D192_ED03))).collect();
        let gamma = F128::new(77, 99);
        let eq = build_eq_table(&r);
        let scaled: Vec<F128> = eq.iter().map(|&e| gamma * e).collect();
        let c = opening::coefficients(gamma, &r, &eq);
        assert_eq!(c, linearized_coefficients(&build_fold_byte_table(&scaled)), "linearised coefficients");
        println!("closed-form coefficients are Flock's ✓");
        let v: Vec<F128> = (0..128u64).map(|i| F128::new(i.wrapping_mul(0x2545_F491_4F6C_DD1D) ^ 5, i + 3)).collect();
        assert_eq!(opening::rooted_sum(gamma, &r, &v), opening::frobenius_sum(&c, &v), "the rooted sum");
        println!("the squaring chain is the sum over Frobenius powers ✓");
    }
    let (opened, _child) = opening::transport(&vk, &mut rd, &mut tr, &p).expect("the mirror accepts the transport");
    assert_eq!(rd.remaining(), 0, "the encoding is read whole");
    assert_eq!(opened.target, opened.value * opened.weight, "the transport's last equation");
    println!("transport: the assist and the last equation hold ✓");
    pofseed_flock_lift_structure::proof::verify(&key.root.structure.verifying(), &claims, &lifted.structure, &mut native_tr).expect("the structure proof verifies");
    let data = pofseed_flock_lift_evm::wrap::encode_lift(&vk, &lifted, &words, claims.cells.1[0], claims.cells.1[1]);
    let t = Instant::now();
    let digest = pofseed_flock_lift_evm::wrap::verify_lift(&vk, &program, &statement, &data).expect("the mirror accepts the lift");
    assert_eq!(digest, native_tr.digest(), "the transcripts end alike");
    println!("lift: {} B of calldata, accepted by the mirror in {:.3} s on the lifter's transcript ✓", data.len(), t.elapsed().as_secs_f64());
    let mut refused = 0;
    for at in (0..data.len()).step_by(data.len() / 997 + 1) {
        let mut bad = data.clone();
        bad[at] ^= 1;
        if pofseed_flock_lift_evm::wrap::verify_lift(&vk, &program, &statement, &bad).is_err() {
            refused += 1;
        } else {
            println!("  a flipped bit at byte {at} is ACCEPTED");
        }
    }
    println!("tampering: {refused} flipped bits refused");
}
