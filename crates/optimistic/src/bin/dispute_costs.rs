// SPDX-License-Identifier: LGPL-3.0-or-later

//! Meters what the simulation does not: a dissection move at several arities, the number of
//! moves a dispute over the whole trace takes at each, the unchallenged path on the lift and
//! matrix proof themselves, and the point evaluation a blob-based upload would need.
//!
//! Usage: `dispute-costs <responses> <lift-cache-file> <trace-steps>`.

use std::env;

use c_kzg::{Blob, Bytes32, ethereum_kzg_settings};
use pofseed_flock_lift_evm::evm::{Abi, artifact, encode};
use pofseed_flock_lift_optimistic::{
    deploy::deploy,
    machine::{Machine, Outcome},
    scenario::{BINDING, Scenario},
};
use revm::primitives::{Address, U256, keccak256};
use sha2::Digest;

const ASSERTER: Address = Address::new([0xa5; 20]);
const CHALLENGER: Address = Address::new([0xc4; 20]);
const CAP: u64 = 1 << 24;
const DAY: u64 = 86_400;

fn ether(n: u64) -> U256 {
    return U256::from(n) * U256::from(10u64).pow(U256::from(18));
}

fn word(out: &Outcome, i: usize) -> U256 {
    return U256::from_be_slice(&out.output[32 * i..32 * i + 32]);
}

/// Moves of the asserter until the interval is one step, the chosen sub-interval always the
/// widest.
fn dissections(steps: u64, arity: u64) -> usize {
    let (mut lo, mut hi, mut moves) = (0u64, steps, 0);
    while hi - lo >= 2 {
        let span = hi - lo;
        let k = span.min(arity);
        let p: Vec<u64> = (0..=k).map(|j| lo + ((span as u128 * j as u128) / k as u128) as u64).collect();
        let j = (0..k as usize).max_by_key(|&j| p[j + 1] - p[j]).unwrap();
        (lo, hi) = (p[j], p[j + 1]);
        moves += 1;
    }
    return moves;
}

fn deploy_dispute(machine: &mut Machine, onestep: Address, arity: u64) -> Address {
    let args = Abi::default()
        .uint(U256::from_be_slice(onestep.as_slice()))
        .uint(ether(1))
        .uint(U256::from(7 * DAY))
        .uint(U256::from(DAY))
        .uint(U256::from(arity))
        .finish(Vec::new());
    let mut code = artifact("Dispute.sol", "Dispute");
    code.extend_from_slice(&args);
    return machine.deploy(code).0;
}

/// Uploads `data` to `dispute`, returning the upload and each transaction's gas.
fn upload(machine: &mut Machine, dispute: Address, data: &[u8], label: &str) -> (U256, Vec<(String, u64)>) {
    let mut gas = Vec::new();
    let out = machine.call_as(ASSERTER, dispute, encode("beginUpload(uint256)", |a| a.uint(U256::from(data.len()))), U256::ZERO);
    assert!(out.success, "beginUpload");
    gas.push((format!("{label}: beginUpload"), out.gas));
    let id = word(&out, 0);
    for (i, chunk) in data.chunks(32 << 13).enumerate() {
        let out = machine.call_as(ASSERTER, dispute, encode("upload(uint256,bytes)", |a| a.uint(id).bytes(chunk)), U256::ZERO);
        assert!(out.success && out.gas <= CAP, "upload chunk {i}");
        gas.push((format!("{label}: chunk {i} ({} bytes)", chunk.len()), out.gas));
    }
    let out = machine.call_as(ASSERTER, dispute, encode("finishUpload(uint256)", |a| a.uint(id)), U256::ZERO);
    assert!(out.success, "finishUpload");
    gas.push((format!("{label}: finishUpload"), out.gas));
    return (id, gas);
}

fn assert_lift(machine: &mut Machine, dispute: Address, scenario: &Scenario, ids: (U256, U256), steps: u64) -> Outcome {
    return machine.call_as(
        ASSERTER,
        dispute,
        encode("assertLift(bytes,uint256,bytes,uint256,uint256,uint256)", |a| {
            a.bytes(&scenario.output).uint(scenario.counts).bytes(BINDING).uint(ids.0).uint(ids.1).uint(U256::from(steps))
        }),
        ether(1),
    );
}

fn main() {
    let n: usize = env::args().nth(1).expect("responses").parse().expect("responses");
    let cache = env::args().nth(2).expect("lift cache file");
    let steps: u64 = env::args().nth(3).expect("trace steps").parse().expect("steps");
    let mut machine = Machine::new(false);
    let scenario = Scenario::new(&mut machine, n, &cache);
    let onestep = deploy(&mut machine, &scenario).onestep;
    machine.fund(ASSERTER, ether(1_000_000));
    machine.fund(CHALLENGER, ether(1_000_000));
    println!("trace of {steps} steps");
    println!("{:>6} {:>12} {:>14} {:>14} {:>16}", "arity", "dissections", "dissect gas", "choose gas", "both sides, all");
    for arity in [2u64, 4, 16, 64, 256, 1024] {
        let dispute = deploy_dispute(&mut machine, onestep, arity);
        let (a, _) = upload(&mut machine, dispute, &scenario.proof[..64], "lift");
        let (b, _) = upload(&mut machine, dispute, &[7u8; 64], "matrix");
        let out = assert_lift(&mut machine, dispute, &scenario, (a, b), steps);
        assert!(out.success, "assertLift");
        let assertion = word(&out, 0);
        let out = machine.call_as(CHALLENGER, dispute, encode("challenge(uint256)", |a| a.uint(assertion)), ether(1));
        assert!(out.success, "challenge");
        let game = word(&out, 0);
        let k = steps.min(arity);
        let mids: Vec<U256> = (1..k).map(|j| U256::from_be_bytes(keccak256(j.to_be_bytes()).0)).collect();
        let d = machine.call_as(ASSERTER, dispute, encode("dissect(uint256,bytes32[])", |a| a.uint(game).uints(&mids)), U256::ZERO);
        assert!(d.success && d.gas <= CAP, "dissect");
        let c = machine.call_as(
            CHALLENGER,
            dispute,
            encode("choose(uint256,bytes32[],uint256)", |a| a.uint(game).uints(&mids).uint(U256::from(k / 2))),
            U256::ZERO,
        );
        assert!(c.success && c.gas <= CAP, "choose");
        let moves = dissections(steps, arity);
        println!("{arity:>6} {moves:>12} {:>14} {:>14} {:>16}", d.gas, c.gas, moves as u64 * (d.gas + c.gas));
    }

    // The unchallenged path on the proofs themselves: uploads, assertion, confirmation.
    let dispute = deploy_dispute(&mut machine, onestep, 16);
    machine.set_time(1_800_000_000);
    let (lift_id, mut honest) = upload(&mut machine, dispute, &scenario.proof, "lift");
    let (matrix_id, gas) = upload(&mut machine, dispute, &scenario.matrix_proof, "matrix proof");
    honest.extend(gas);
    let out = assert_lift(&mut machine, dispute, &scenario, (lift_id, matrix_id), steps);
    assert!(out.success, "assertLift");
    honest.push(("assertLift".to_string(), out.gas));
    let assertion = word(&out, 0);
    machine.set_time(1_800_000_000 + 7 * DAY);
    let out = machine.call_as(ASSERTER, dispute, encode("confirm(uint256)", |a| a.uint(assertion)), U256::ZERO);
    assert!(out.success, "confirm");
    honest.push(("confirm".to_string(), out.gas));
    println!("unchallenged path ({} + {} proof bytes):", scenario.proof.len(), scenario.matrix_proof.len());
    for (label, gas) in &honest {
        println!("  {label:<40} {gas:>10}");
    }
    println!("  {:<40} {:>10} in {} transactions", "in all", honest.iter().map(|h| h.1).sum::<u64>(), honest.len());

    // Blobs: the proofs as field elements of 31 bytes each, 4096 to a blob.
    let per_blob = 4096 * 31;
    let bytes = scenario.proof.len() + scenario.matrix_proof.len();
    let blobs = bytes.div_ceil(per_blob);
    let settings = ethereum_kzg_settings(0);
    let mut blob = vec![0u8; 4096 * 32];
    for (i, chunk) in scenario.proof[..per_blob.min(scenario.proof.len())].chunks(31).enumerate() {
        blob[i * 32 + 1..i * 32 + 1 + chunk.len()].copy_from_slice(chunk);
    }
    let blob = Blob::from_bytes(&blob).expect("blob");
    let commitment = settings.blob_to_kzg_commitment(&blob).expect("commitment");
    let z = Bytes32::from([0u8; 32]);
    let (kzg_proof, y) = settings.compute_kzg_proof(&blob, &z).expect("proof");
    let mut versioned: [u8; 32] = sha2::Sha256::digest(commitment.to_bytes().as_slice()).into();
    versioned[0] = 0x01;
    let mut input = versioned.to_vec();
    input.extend_from_slice(&*z);
    input.extend_from_slice(&*y);
    input.extend_from_slice(commitment.to_bytes().as_slice());
    input.extend_from_slice(kzg_proof.to_bytes().as_slice());
    let pe = Address::with_last_byte(0x0a);
    let out = machine.call_as(ASSERTER, pe, input.clone(), U256::ZERO);
    assert!(out.success, "the point evaluation verifies");
    let mut bad = input.clone();
    bad[64] ^= 1;
    let refused = machine.call_as(ASSERTER, pe, bad, U256::ZERO);
    assert!(!refused.success, "a wrong value is refused");
    let zeros = input.iter().filter(|&&b| b == 0).count() as u64;
    let intrinsic = 21_000 + 4 * zeros + 16 * (input.len() as u64 - zeros);
    println!(
        "proofs of {bytes} bytes: {blobs} blobs of 4096 elements at 31 bytes each; one point evaluation: {} gas in all, {} of it the precompile",
        out.gas,
        out.gas - intrinsic
    );
}
