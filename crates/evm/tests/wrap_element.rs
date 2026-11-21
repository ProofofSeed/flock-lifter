// SPDX-License-Identifier: LGPL-3.0-or-later

//! The wrap contracts refuse element-table evaluations that are not the tables', in one call and
//! in stages, as Flock's own verifier does; the contracts are built in a copy of the verifier's
//! project with the constants of this test's shape.

use std::{path::PathBuf, sync::Arc};

use flock_prover::{field::F128, pcs::OuterPcs};
use pofseed_flock_lift::{
    lift::Statement,
    root,
    wrap::outer_transcript,
    wrapped::{self, WrappedLift},
};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    evm::{Evm, artifact_at, build_wrap_at, encode},
    wrap::{self, sol, staged, vk::Vk},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
};
use revm::primitives::{U256, keccak256};

const BINDING: &[u8] = b"flock-lifter element table binding";

#[test]
fn shifted_element_matrix_evaluations_are_refused_on_chain() {
    let (n, chunk, rate) = (8, 4, 1);
    let whir = WhirOuter::new(4, rate, Regime::Johnson, 3, 22, 128).with_merkle(MerkleHash::Keccak);
    let outer = Some(&whir as &dyn OuterPcs);
    let (_, chain_code) = bip32_vector_1();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter element table entropy", BINDING);
    let statement = Statement {
        chain_code,
        index: HARDENED_OFFSET,
        expected_output: output.clone(),
        binding: BINDING.to_vec(),
    };
    let (key, lifted, _) = wrapped::prove(&program, &statement, &proof, chunk, &whir, None, rate).expect("a lift");
    wrapped::verify(&program, &key, &statement, &lifted, &whir).expect("the lift verifies");
    let words = wrapped::words(&program, &key, &lifted).expect("published words");
    let counts = (output.as_vec::<u8>().len() | (output.as_vec::<u32>().len() << 16) | (output.as_vec::<u64>().len() << 32)) as u64;
    let vk = Vk::new(&key, whir.config(key.wrap.key.pcs.m - 7), words[0].len(), counts);
    let (claims, _) = root::outer_claims(&key.wrap, &key.root.table_of, &lifted.wrap, outer).expect("the outer proof verifies");
    let (live, masked) = (claims.cells.1[0], claims.cells.1[1]);
    let (work, _) = key.wrap.key.verify_deferred(&lifted.wrap, outer, &mut outer_transcript(&lifted.wrap.public)).expect("the deferred verification");
    let alpha = work.element.expect("an element class").alpha;
    let mut forged: WrappedLift = lifted.clone();
    let evals = &mut forged.wrap.proof.element.as_mut().expect("an element proof").lincheck.matrix_evals;
    evals[0].0 += alpha;
    evals[0].1 += F128::ONE;
    assert!(
        key.wrap.key.verify_on(&forged.wrap, outer, &mut outer_transcript(&forged.wrap.public)).is_err(),
        "Flock's own verifier refuses the shifted evaluations"
    );
    let honest = wrap::encode_lift(&vk, &lifted, &words, live, masked);
    let shifted = wrap::encode_lift(&vk, &forged, &words, live, masked);
    assert_eq!(honest.len(), shifted.len(), "the forgery changes values, not the encoding's shape");
    wrap::verify_lift(&vk, &program, &statement, &honest).expect("the mirror accepts the honest lift");
    assert_eq!(
        wrap::verify_lift(&vk, &program, &statement, &shifted).map(|_| ()).map_err(|e| e.0),
        Err("element table evaluation"),
        "the mirror refuses the shifted evaluations"
    );

    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("wrap-element-verifier");
    build_wrap_at(&dir, &sol::key_source(&vk));
    let refusal = keccak256(b"ElementTable()")[..4].to_vec();
    let output_bytes = output.as_bytes();
    let call = |lift: &[u8]| encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&output_bytes).uint(U256::from(counts)).bytes(BINDING).bytes(lift));

    let mut evm = Evm::new();
    let (address, _) = evm.deploy(artifact_at(&dir, "FlockWrap.sol", "FlockWrap"));
    let out = evm.simulate(address, call(&honest));
    println!("single call, honest lift: success {}, gas {}", out.success, out.gas);
    assert!(out.success, "the single call accepts the honest lift: {}", hex::encode(&out.output));
    let out = evm.simulate(address, call(&shifted));
    println!("single call, shifted evaluations: success {}, revert data {}", out.success, hex::encode(&out.output));
    assert!(!out.success, "the single call refuses the shifted evaluations");
    assert_eq!(out.output, refusal, "the single call refuses with ElementTable");

    // At this shape the tables' opening stage exceeds the code-size limit, so the stages run uncapped.
    let (mut chain, mut probe) = (Evm::new(), Evm::new());
    let deployment = staged::deploy_at(&mut chain, &sol::key_source(&vk), &dir);
    staged::deploy_at(&mut probe, &sol::key_source(&vk), &dir);
    let (txs, digest) = staged::verify(&mut chain, &mut probe, deployment.sessions, U256::from(1), &output_bytes, counts, BINDING, &honest)
        .unwrap_or_else(|(stage, data)| panic!("stage {stage} refused the honest lift: {}", hex::encode(data)));
    println!("staged, honest lift: accepted in {} transactions", txs.len());
    assert!(staged::accepted(&mut chain, deployment.sessions, &digest), "the session accepts the statement");
    let refused = staged::verify(&mut chain, &mut probe, deployment.sessions, U256::from(2), &output_bytes, counts, BINDING, &shifted);
    let (stage, data) = refused.err().expect("the staged verifier refuses the shifted evaluations");
    println!("staged, shifted evaluations: refused at stage {stage} ({}), revert data {}", staged::stage_name(stage), hex::encode(&data));
    assert_eq!(stage, 2, "the element class's stage refuses");
    assert_eq!(data, refusal, "the staged verifier refuses with ElementTable");
}
