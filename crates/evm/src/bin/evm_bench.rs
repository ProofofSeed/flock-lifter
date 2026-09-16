// SPDX-License-Identifier: LGPL-3.0-or-later

//! Meters the on-chain verification of a lifted hardened-child proof: the lift contract over
//! every chunk and the Fiat-Shamir gate, then the matrix discharge, each phase in its own
//! transaction-sized call, in an in-process EVM with no gas cap.
//!
//! Usage: `evm-bench <responses> [lift-cache-file] [bytes-per-segment]`.

use std::{env, fs, sync::Arc, time::Instant};

use pofseed_flock_lift::lift::{MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::encode_lift,
    discharge::{Stream, deploy, run},
    evm::{Evm, Outcome, artifact, encode},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit};
use revm::primitives::U256;
use zkboo_circuit_hash::hash_circuit;

const BINDING: &[u8] = b"flock-lifter evm-bench binding";
const ENTROPY: &[u8] = b"flock-lifter evm-bench entropy";
const TX_CAP: u64 = 1 << 24;

fn label(id: u64) -> String {
    return match id {
        1 => "published words".into(),
        2 => "zerocheck".into(),
        3 => "lincheck".into(),
        4 => "published-word claim".into(),
        10 => "ring switches".into(),
        11 => "Ligerito level 0 opening".into(),
        12..=19 => format!("Ligerito level {} opening", id - 11),
        20 => "Ligerito final opening".into(),
        21 => "ring-switch residual".into(),
        22 => "out-of-domain residual".into(),
        23 => "consistency residual".into(),
        5 => "final check".into(),
        101 => "Fiat-Shamir gate".into(),
        other => format!("phase {other}"),
    };
}

/// The gas spent between consecutive marks, labelled by the mark that closes each span.
fn phases(out: &Outcome) -> Vec<(u64, u64)> {
    let mut spans = Vec::new();
    let mut last: Option<u64> = None;
    for (topics, body) in &out.logs {
        let id = U256::from_be_bytes(topics[1]).to::<u64>();
        let left = U256::from_be_slice(&body[..32]).to::<u64>();
        if let Some(prev) = last {
            spans.push((id, prev - left));
        }
        last = Some(left);
    }
    return spans;
}

fn mgas(g: u64) -> String {
    return format!("{:.2} M", g as f64 / 1e6);
}

fn main() {
    let n: usize = env::args().nth(1).map_or(219, |s| s.parse().expect("response count"));
    let cache = env::args().nth(2);
    let segment_bytes: usize = env::args().nth(3).map_or(usize::MAX, |s| s.parse().expect("bytes per segment"));
    let (_, chain_code) = bip32_vector_1();
    let (_, output, proof) = vector_1_proof(n, ENTROPY, BINDING);
    let statement = Statement {
        chain_code: chain_code.clone(),
        index: HARDENED_OFFSET,
        expected_output: output,
        binding: BINDING.to_vec(),
    };
    let t = Instant::now();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    println!("block built in {:.2} s", t.elapsed().as_secs_f64());
    let lifted = match cache.as_deref().and_then(|p| fs::read(p).ok()) {
        Some(bytes) => bincode::deserialize(&bytes).expect("cached lift"),
        None => {
            let t = Instant::now();
            let lifted = prove(&program, &statement, &proof, MAX_CHUNK).expect("lift");
            println!("lift proved in {:.2} s", t.elapsed().as_secs_f64());
            if let Some(p) = cache.as_deref() {
                fs::write(p, bincode::serialize(&lifted).expect("serialise")).expect("write cache");
            }
            lifted
        }
    };
    verify(&program, &statement, &lifted).expect("the native verifier accepts");
    let data = encode_lift(&lifted);
    println!("responses {n}, chunks {}, lift calldata {} bytes", lifted.chunks.len(), data.len());

    let mut evm = Evm::new();
    let mut code = artifact("FlockLift.sol", "FlockLift");
    let runtime_len = code.len();
    code.extend_from_slice(&hash_circuit::<_, H>(&statement.circuit()));
    code.extend_from_slice(&chain_code);
    code.extend_from_slice(&U256::from(HARDENED_OFFSET).to_be_bytes::<32>());
    code.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
    let (lift, lift_deploy) = evm.deploy(code);
    println!("FlockLift: initcode {runtime_len} bytes, deployment {} gas", lift_deploy);
    let y = &statement.expected_output;
    let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
    let call = encode("verify(bytes,uint256,bytes,bytes)", |a| {
        a.bytes(&y.as_bytes()).uint(counts).bytes(BINDING).bytes(&data)
    });
    let t = Instant::now();
    let out = evm.call(lift, call);
    assert!(out.success, "the lift contract refused: {}", hex::encode(&out.output));
    println!("lift contract ran in {:.2} s", t.elapsed().as_secs_f64());
    let mut chunk = 0;
    for (id, gas) in phases(&out) {
        if id == 1 {
            chunk += 1;
            println!("chunk {chunk}:");
        }
        println!("  {:<28} {:>14}", label(id), mgas(gas));
    }
    println!(
        "lift contract: {} total = {} execution + {} intrinsic (calldata)",
        mgas(out.gas),
        mgas(out.execution()),
        mgas(out.intrinsic)
    );
    let claims: Vec<U256> = (0..U256::from_be_slice(&out.output[32..64]).to::<usize>())
        .map(|i| U256::from_be_slice(&out.output[64 + 32 * i..96 + 32 * i]))
        .collect();

    let t = Instant::now();
    let stream = Stream::new(&program, segment_bytes);
    let discharge = deploy(&mut evm, &program, &stream);
    println!(
        "FlockDischarge deployed; stream of {} bytes in {} segments, {} head words ({:.1} s to build)",
        stream.len(),
        stream.segments.len(),
        stream.head_words,
        t.elapsed().as_secs_f64()
    );
    let t = Instant::now();
    let gas = run(&mut evm, discharge, &stream, &claims);
    assert!(gas.accepted, "the discharge refused genuine claims");
    let rows_exec: u64 = gas.rows.iter().sum();
    let rows_data: u64 = gas.rows_calldata.iter().sum();
    println!("discharge ran in {:.1} s", t.elapsed().as_secs_f64());
    println!("discharge, {} claims:", claims.len() / 112);
    println!("  {:<28} {:>14}", "Keccak-f sub-blocks", mgas(gas.keccak));
    println!("  {:<28} {:>14} execution + {} calldata", "stream", mgas(rows_exec), mgas(rows_data));
    println!("  {:<28} {:>14}", "  of it, per-call tables", mgas(gas.setup.iter().sum()));
    println!("  {:<28} {:>14}", "final check", mgas(gas.finish));
    let total_exec = out.execution() + gas.keccak + rows_exec + gas.finish;
    let total = out.gas + gas.keccak + rows_exec + rows_data + gas.finish + gas.intrinsic;
    println!("verification in all: {} gas, {} of it execution", mgas(total), mgas(total_exec));
    println!("at least {} transactions under the {}-gas cap", total.div_ceil(TX_CAP), TX_CAP);
}
