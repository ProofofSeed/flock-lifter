// SPDX-License-Identifier: LGPL-3.0-or-later
//! Flock's union-circuit prover with WHIR as its outer commitment: honest proofs verify, and
//! tampered openings or a mismatched commitment scheme are refused.

use flock_prover::challenger::FsChallenger;
use flock_prover::circuit::{Cell, Circuit};
use flock_prover::element_r1cs::ElementTableBuilder;
use flock_prover::field::F128;
use flock_prover::pcs::ligerito::{LigeritoProfile, embedded_initial_k_or_default};
use flock_prover::pcs::{MergedInner, OuterPcs, PcsParams};
use flock_prover::prover::{
    UnionElementSlotInput, UnionSlotProverInput, prove_union_circuit_ag_with_outer,
};
use flock_prover::r1cs_hashes::sha2::{
    SHA256_IV, build_block_r1cs, generate_witness_batch_major_partial, sha256_compress,
};
use flock_prover::schedule::{IoWord, Registry, TableType};
use flock_prover::union::UnionInstance;
use flock_prover::verifier::verify_union_circuit_ag_deferred_with_outer;
use pofseed_flock_lift_whir::outer::WhirOuter;
use std::sync::Arc;

const DOMAIN: &[u8] = b"flock-whir-outer-test";

fn words(u32s: &[u32]) -> Vec<F128> {
    u32s.chunks(4)
        .map(|c| {
            F128::new(c[0] as u64 | ((c[1] as u64) << 32), c[2] as u64 | ((c[3] as u64) << 32))
        })
        .collect()
}

#[test]
fn a_circuit_proof_opens_through_whir() {
    let nu = 7;
    let r1cs = build_block_r1cs(nu);
    let mut mult = ElementTableBuilder::new(2);
    mult.free_wire(0).free_wire(1).mult(2, 0, 1);
    let registry = Registry::new(
        vec![
            TableType::element(Arc::new(mult.build().unwrap())).with_io_schema(vec![
                IoWord::input(0),
                IoWord::input(1),
                IoWord::output(2),
            ]),
            TableType::from_block_r1cs(&r1cs).with_io_schema(vec![
                IoWord::input(0),
                IoWord::input(1),
                IoWord::input(4),
                IoWord::input(5),
                IoWord::input(6),
                IoWord::input(7),
                IoWord::output(2),
                IoWord::output(3),
            ]),
        ],
        nu,
    );
    let m: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x9E37_79B9) ^ 0x5A5A_1234);
    let out = words(&sha256_compress(&SHA256_IV, &m));
    let mut public = words(&SHA256_IV);
    public.extend(words(&m));
    public.push(out[0] * out[1]);
    let (sha, el) = (0, 8);
    let wires = vec![
        vec![Cell::new(11, 0), Cell::new(sha, 0)],
        vec![Cell::new(11, 1), Cell::new(sha + 1, 0)],
        vec![Cell::new(11, 2), Cell::new(sha + 2, 0)],
        vec![Cell::new(11, 3), Cell::new(sha + 3, 0)],
        vec![Cell::new(11, 4), Cell::new(sha + 4, 0)],
        vec![Cell::new(11, 5), Cell::new(sha + 5, 0)],
        vec![Cell::new(sha + 6, 0), Cell::new(el, 0)],
        vec![Cell::new(sha + 7, 0), Cell::new(el + 1, 0)],
        vec![Cell::new(el + 2, 0), Cell::new(11, 6)],
    ];
    let counts = vec![1usize, 1];
    let union = UnionInstance::new(&registry, counts.clone());
    let k = embedded_initial_k_or_default(union.dense_m(), LigeritoProfile::Fast);
    let params = PcsParams {
        m: union.dense_m(),
        log_inv_rate: 1,
        log_batch_size: k,
        profile: LigeritoProfile::Fast,
        num_lanes: union.commit_lanes(k),
        merkle_hash: Default::default(),
    };
    let circuit = Circuit::new(&registry, counts, public.len(), wires).unwrap();
    let el_width = registry.types()[1].element_type().unwrap().width();
    let mut z = vec![F128::ZERO; el_width << nu];
    z[0] = out[0];
    z[1 << nu] = out[1];
    z[2 << nu] = out[0] * out[1];
    let lincheck = r1cs.csc_lincheck_circuit();
    let outer = WhirOuter::new(4, 1, pofseed_flock_lift_whir::params::Regime::Johnson, 4, 8, 100);
    let (proof, commitment, _) = prove_union_circuit_ag_with_outer(
        &union,
        &circuit,
        &public,
        &params,
        vec![UnionSlotProverInput::new(
            generate_witness_batch_major_partial(&[(SHA256_IV, m)], nu),
            lincheck,
        )],
        vec![UnionElementSlotInput::new(move |dst: &mut [F128]| dst.copy_from_slice(&z))],
        Some(&outer),
        &mut FsChallenger::new(DOMAIN),
    );
    assert!(matches!(proof.pcs_open.inner, MergedInner::Outer(_)));
    let verify = |p: &_, o: Option<&dyn OuterPcs>| {
        verify_union_circuit_ag_deferred_with_outer(
            &union,
            &circuit,
            &public,
            &[lincheck],
            &commitment,
            p,
            &params,
            o,
            &mut FsChallenger::new(DOMAIN),
        )
    };
    verify(&proof, Some(&outer)).expect("an honest proof verifies");
    assert!(verify(&proof, None).is_err(), "Ligerito cannot check a WHIR opening");
    let mut tampered = proof.clone();
    if let MergedInner::Outer(bytes) = &mut tampered.pcs_open.inner {
        let n = bytes.len();
        bytes[n / 2] ^= 1;
    }
    assert!(verify(&tampered, Some(&outer)).is_err(), "a tampered WHIR opening");
    let mut tampered = proof.clone();
    tampered.pcs_open.q_eval += F128::ONE;
    assert!(verify(&tampered, Some(&outer)).is_err(), "another value at the merged point");
}
