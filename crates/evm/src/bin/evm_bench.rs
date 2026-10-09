// SPDX-License-Identifier: LGPL-3.0-or-later

//! Meters the on-chain verification of a lifted hardened-child proof: the lift contract over
//! every chunk and the Fiat-Shamir gate, then the matrix discharge, each phase in its own
//! transaction-sized call, in an in-process EVM with no gas cap.
//!
//! The matrix claims are discharged through the committed entry list by default, or, with
//! `POFSEED_EVM_DISCHARGE=stream`, by the row stream the contract walks. The committed route is then
//! run again as the staged verifier, in transactions under mainnet's gas cap from contracts under
//! its code-size limit, unless `POFSEED_EVM_STAGED=0`.
//!
//! Usage: `evm-bench <responses> [lift-cache-file] [bytes-per-segment]`.

use std::{env, fs, sync::Arc, time::Instant};

use pofseed_flock_lift::lift::{LiftKey, MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::{encode_lift, encode_matrix},
    committed,
    discharge::{Stream, deploy, run},
    evm::{Evm, Outcome, artifact, encode},
    staged,
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
        301 => "claims and structured parts".into(),
        302 => "matrix main sumcheck".into(),
        303 => "matrix count claim".into(),
        304 => "matrix count sumcheck".into(),
        305 => "matrix address bits".into(),
        306 => "final check".into(),
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

struct Staged<'a> {
    fingerprint: &'a [u8; 32],
    chain_code: &'a [u8],
    n: usize,
    chunk: usize,
    program: &'a Program,
    key: &'a pofseed_flock_lift::matrix::MatrixCommitment,
    slim: bool,
    output: &'a [u8],
    counts: U256,
    lift: &'a [u8],
    matrix: &'a [u8],
    claims: &'a [U256],
    digest: &'a [u8; 32],
}

fn report(label: &str, session: &staged::Session) -> (u64, usize) {
    println!("{label} session:");
    let mut stages: Vec<(u64, usize, u64, u64, u64)> = Vec::new();
    for t in &session.txs {
        match stages.last_mut() {
            Some(s) if s.0 == t.stage => {
                s.1 += 1;
                s.2 += t.gas;
                s.3 += t.intrinsic;
                s.4 = s.4.max(t.gas);
            }
            _ => stages.push((t.stage, 1, t.gas, t.intrinsic, t.gas)),
        }
    }
    let mut merged: Vec<(u64, usize, u64, u64, u64)> = Vec::new();
    for s in stages {
        match merged.iter_mut().find(|m| m.0 == s.0) {
            Some(m) => {
                m.1 += s.1;
                m.2 += s.2;
                m.3 += s.3;
                m.4 = m.4.max(s.4);
            }
            None => merged.push(s),
        }
    }
    for (stage, count, gas, intrinsic, max) in &merged {
        let name = if *stage == 0 { "session start" } else { staged::stage_name(*stage) };
        println!(
            "  {:<28} {:>4} txs {:>14} ({} calldata), largest {}",
            name,
            count,
            mgas(*gas),
            mgas(*intrinsic),
            mgas(*max)
        );
    }
    if std::env::var("POFSEED_EVM_TXS").as_deref() == Ok("1") {
        for t in &session.txs {
            println!(
                "    tx stage {:>2} items {:>4}..{:<4} {:>10} gas, {:>8} calldata gas, state {:>6} B, data {:>7} B",
                t.stage, t.items.0, t.items.1, t.gas, t.intrinsic, t.state, t.data
            );
        }
    }
    let total: u64 = session.txs.iter().map(|t| t.gas).sum();
    let largest = session.txs.iter().map(|t| t.gas).max().unwrap_or(0);
    println!("  {} transactions, {} in all, largest {}", session.txs.len(), mgas(total), mgas(largest));
    return (total, session.txs.len());
}

fn run_staged(s: &Staged) {
    let t = Instant::now();
    let mut evm = Evm::mainnet();
    let dep = staged::deploy(
        &mut evm,
        s.fingerprint,
        s.chain_code,
        HARDENED_OFFSET,
        s.n,
        s.counts,
        s.program,
        s.key,
        s.slim,
    );
    println!("staged verifier, under the {TX_CAP}-gas cap and the 24,576-byte code limit:");
    let mut deployment = 0;
    for (name, size, gas) in &dep.contracts {
        println!("  {:<28} {:>6} bytes, deployment {}", name, size, mgas(*gas));
        deployment += gas;
    }
    println!("  deployment in all {}", mgas(deployment));
    let lift = staged::lift(&mut evm, dep.sessions, U256::from(1), s.output, s.counts, BINDING, s.lift, s.n, s.chunk)
        .expect("the staged lift refused");
    let (recorded, _) = staged::recorded(&mut evm, dep.sessions, s.digest);
    let packed: Vec<u8> = s.claims.iter().flat_map(|c| c.to_be_bytes::<32>()).collect();
    assert_eq!(recorded, U256::from_be_bytes(revm::primitives::keccak256(&packed).0), "recorded claims differ");
    let matrix = staged::matrix(&mut evm, dep.sessions, U256::from(2), s.digest, s.claims, s.matrix)
        .expect("the staged matrix verification refused");
    let (_, accepted) = staged::recorded(&mut evm, dep.sessions, s.digest);
    assert!(accepted, "the session contract did not accept the lift");
    let (lg, lt) = report("lift", &lift);
    let (mg, mt) = report("matrix", &matrix);
    println!(
        "staged verification in all: {} in {} transactions, every one under the cap ({:.1} s)",
        mgas(lg + mg),
        lt + mt,
        t.elapsed().as_secs_f64()
    );
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
    let key = LiftKey::new(program.clone());
    let lifted = match cache.as_deref().and_then(|p| fs::read(p).ok()) {
        Some(bytes) => bincode::deserialize(&bytes).expect("cached lift"),
        None => {
            let t = Instant::now();
            let lifted = prove(&key, &statement, &proof, MAX_CHUNK).expect("lift");
            println!("lift proved in {:.2} s", t.elapsed().as_secs_f64());
            if let Some(p) = cache.as_deref() {
                fs::write(p, bincode::serialize(&lifted).expect("serialise")).expect("write cache");
            }
            lifted
        }
    };
    verify(&key.verifying(), &statement, &lifted).expect("the native verifier accepts");
    let data = encode_lift(&lifted);
    let lift_data = data.clone();
    println!("responses {n}, chunks {}, lift calldata {} bytes", lifted.chunks.len(), data.len());

    let mut evm = Evm::new();
    let mut code = artifact("FlockLift.sol", "FlockLift");
    let runtime_len = code.len();
    code.extend_from_slice(&hash_circuit::<_, H>(&statement.circuit()));
    code.extend_from_slice(&chain_code);
    code.extend_from_slice(&U256::from(HARDENED_OFFSET).to_be_bytes::<32>());
    code.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
    let y = &statement.expected_output;
    let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
    code.extend_from_slice(&counts.to_be_bytes::<32>());
    let slim = pofseed_flock_lift::chunk_rm::profile() == flock_prover::pcs::ligerito::LigeritoProfile::Slim;
    code.extend_from_slice(&U256::from(slim as u8).to_be_bytes::<32>());
    let (lift, lift_deploy) = evm.deploy(code);
    println!("FlockLift: initcode {runtime_len} bytes, deployment {} gas", lift_deploy);
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
    let (lift_gas, lift_exec) = (out.gas, out.execution());
    let claims: Vec<U256> = (0..U256::from_be_slice(&out.output[32..64]).to::<usize>())
        .map(|i| U256::from_be_slice(&out.output[64 + 32 * i..96 + 32 * i]))
        .collect();

    if std::env::var("POFSEED_EVM_DISCHARGE").as_deref() != Ok("stream") {
        let digest = statement.digest(n, lifted.chunk);
        let vk = key.verifying();
        let (matrix_at, matrix_deploy) = committed::deploy_matrix(&mut evm, &program, &vk.matrix, slim);
        let data = encode_matrix(lifted.matrix.as_ref().expect("a matrix proof"), &vk.matrix);
        let t = Instant::now();
        let out = committed::verify(&mut evm, matrix_at, &claims, &digest, &data);
        assert!(out.success, "the matrix contract refused: {}", hex::encode(&out.output));
        println!("FlockMatrix: deployment {matrix_deploy} gas; ran in {:.2} s", t.elapsed().as_secs_f64());
        println!("discharge, {} claims:", claims.len() / 112);
        for (id, gas) in phases(&out) {
            println!("  {:<28} {:>14}", label(id), mgas(gas));
        }
        println!(
            "matrix contract: {} total = {} execution + {} intrinsic (calldata {} bytes)",
            mgas(out.gas),
            mgas(out.execution()),
            mgas(out.intrinsic),
            data.len()
        );
        let total_exec = lift_exec + out.execution();
        let total = lift_gas + out.gas;
        println!("verification in all: {} gas, {} of it execution", mgas(total), mgas(total_exec));
        println!("at least {} transactions under the {}-gas cap", total.div_ceil(TX_CAP), TX_CAP);
        if std::env::var("POFSEED_EVM_STAGED").as_deref() != Ok("0") {
            let fingerprint = hash_circuit::<_, H>(&statement.circuit());
            let bytes = y.as_bytes();
            run_staged(&Staged {
                fingerprint: &fingerprint,
                chain_code: &chain_code,
                n,
                chunk: lifted.chunk as usize,
                program: &program,
                key: &vk.matrix,
                slim,
                output: &bytes,
                counts,
                lift: &lift_data,
                matrix: &data,
                claims: &claims,
                digest: &digest,
            });
        }
        return;
    }
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
