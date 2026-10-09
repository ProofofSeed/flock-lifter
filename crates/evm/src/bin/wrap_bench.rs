// SPDX-License-Identifier: LGPL-3.0-or-later

//! Lifts a hardened-child proof through the wrap, writes the contract's constants for it, runs
//! the wrap contract on the lift in an in-process EVM, checks it stage by stage against the
//! mirror, and reports the gas of every stage.
//!
//! Usage: `wrap-bench [responses] [chunk] [outer log inverse rate] [tables' log inverse rate] [stop]`
//! (default 8, 4, 1, 1, none).
//! A lift is kept under `target/wrap-cache` and reused; `POFSEED_WRAP_FRESH` makes a new one.
//! The constants' source is put back as it was when the run ends, unless `POFSEED_WRAP_KEEP` is
//! set, which is how the committed constants are regenerated.

use std::{env, fs, path::PathBuf, sync::Arc, time::Instant};

use pofseed_flock_lift::{lift::Statement, root, wrapped};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    evm::{Evm, artifact, encode, project, runtime_len},
    wrap::{self, sol, trace, vk::Vk},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::HardenedChildCircuit;
use pofseed_flock_lift_whir::{
    outer::WhirOuter,
    params::{MerkleHash, Regime},
};
use revm::primitives::U256;

const BINDING: &[u8] = b"flock-lifter wrap bench binding";

/// What a run needs of a lift: the constants' source, the calldata, the expected output with its
/// word counts, and the mirror's checkpoints.
struct Case {
    key: String,
    lift: Vec<u8>,
    output: Vec<u8>,
    counts: u64,
    marks: Vec<(u32, [u8; 32])>,
}

fn cache(n: usize, chunk: usize, rate: usize, tables: usize) -> PathBuf {
    return PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("../../target/wrap-cache/{n}-{chunk}-{rate}-{tables}"));
}

fn load(dir: &PathBuf) -> Option<Case> {
    let marks = fs::read(dir.join("marks")).ok()?;
    let counts = fs::read(dir.join("counts")).ok()?;
    return Some(Case {
        key: fs::read_to_string(dir.join("WrapKey.sol")).ok()?,
        lift: fs::read(dir.join("lift")).ok()?,
        output: fs::read(dir.join("output")).ok()?,
        counts: u64::from_be_bytes(counts.try_into().ok()?),
        marks: marks.chunks(36).map(|c| (u32::from_be_bytes(c[..4].try_into().unwrap()), c[4..].try_into().unwrap())).collect(),
    });
}

fn make(n: usize, chunk: usize, rate: usize, tables: usize, dir: &PathBuf) -> Case {
    let whir = WhirOuter::new(4, rate, Regime::Johnson, 3, 22, 128).with_merkle(MerkleHash::Keccak);
    let (_, chain_code) = bip32_vector_1();
    let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
    let (_, output, proof) = vector_1_proof(n, b"flock-lifter wrap bench entropy", BINDING);
    let statement = Statement {
        chain_code,
        index: HARDENED_OFFSET,
        expected_output: output.clone(),
        binding: BINDING.to_vec(),
    };
    let t = Instant::now();
    let (key, lifted, tm) = wrapped::prove(&program, &statement, &proof, chunk, &whir, None, tables).expect("a lift");
    println!(
        "lifted {n} responses in {:.1} s: chunks {:.1} s, wrap {:.1} s, tables committed in {:.1} s, structure proof {:.1} s",
        t.elapsed().as_secs_f64(),
        tm.chunks,
        tm.wrap.record + tm.wrap.tapes + tm.wrap.build + tm.wrap.witness + tm.wrap.prove,
        tm.key,
        tm.structure
    );
    wrapped::verify(&program, &key, &statement, &lifted, &whir).expect("the lift verifies");
    let words = wrapped::words(&program, &key, &lifted).expect("published words");
    let counts = (output.as_vec::<u8>().len() | (output.as_vec::<u32>().len() << 16) | (output.as_vec::<u64>().len() << 32)) as u64;
    let vk = Vk::new(&key, whir.config(key.wrap.key.pcs.m - 7), words[0].len(), counts);
    let (claims, _) = root::outer_claims(&key.wrap, &key.root.table_of, &lifted.wrap, Some(&whir)).expect("the outer proof verifies");
    let lift = wrap::encode_lift(&vk, &lifted, &words, claims.cells.1[0], claims.cells.1[1]);
    trace::take();
    wrap::verify_lift(&vk, &program, &statement, &lift).expect("the mirror accepts the lift");
    let case = Case {
        key: sol::key_source(&vk),
        lift,
        output: output.as_bytes(),
        counts,
        marks: trace::take(),
    };
    fs::create_dir_all(dir).expect("cache directory");
    fs::write(dir.join("WrapKey.sol"), &case.key).unwrap();
    fs::write(dir.join("lift"), &case.lift).unwrap();
    fs::write(dir.join("output"), &case.output).unwrap();
    fs::write(dir.join("counts"), case.counts.to_be_bytes()).unwrap();
    let marks: Vec<u8> = case.marks.iter().flat_map(|(id, s)| [id.to_be_bytes().to_vec(), s.to_vec()].concat()).collect();
    fs::write(dir.join("marks"), marks).unwrap();
    return case;
}

/// Runs the staged verifier on `case` under mainnet's limits, and reports every transaction.
fn staged_run(case: &Case) {
    use pofseed_flock_lift_evm::{evm::TX_CAP, wrap::staged};
    let (mut chain, mut probe) = (Evm::mainnet(), Evm::new());
    let dep = staged::deploy(&mut chain, &case.key);
    let dep_probe = staged::deploy(&mut probe, &case.key);
    assert_eq!(dep.sessions, dep_probe.sessions, "both chains deploy alike");
    println!("staged verifier:");
    let mut deployment = 0;
    for (name, size, gas) in &dep.contracts {
        println!("  {name:<18} runtime {size:>6} B, deployment {gas:>9} gas");
        deployment += gas;
    }
    println!("  deployment in all {deployment} gas");
    let (txs, digest) = staged::verify(&mut chain, &mut probe, dep.sessions, U256::from(1), &case.output, case.counts, BINDING, &case.lift)
        .unwrap_or_else(|(stage, data)| panic!("stage {stage} refused: {}", hex::encode(&data[..data.len().min(68)])));
    assert!(staged::accepted(&mut chain, dep.sessions, &digest), "the session accepts the statement");
    let mut total = 0;
    for tx in &txs {
        println!(
            "  transaction {}: {:>9} gas ({:>5.1}% of the cap), {:>6} B of the lift, {:>5} B of state: {}",
            tx.stage,
            tx.gas,
            100.0 * tx.gas as f64 / TX_CAP as f64,
            tx.data,
            tx.state,
            staged::stage_name(tx.stage)
        );
        assert!(tx.gas <= TX_CAP, "a transaction exceeds the cap");
        total += tx.gas;
    }
    println!("staged verification: {total} gas in {} transactions, each under the cap; the statement is accepted", txs.len());
    let mut refused = 0;
    for at in (0..case.lift.len()).step_by(case.lift.len() / 11 + 1) {
        let mut bad = case.lift.clone();
        bad[at] ^= 1;
        let (mut chain, mut probe) = (Evm::mainnet(), Evm::new());
        let dep = staged::deploy(&mut chain, &case.key);
        staged::deploy(&mut probe, &case.key);
        match staged::verify(&mut chain, &mut probe, dep.sessions, U256::from(1), &case.output, case.counts, BINDING, &bad) {
            Ok(_) => println!("  a flipped bit at byte {at} is ACCEPTED by the staged verifier"),
            Err(_) => refused += 1,
        }
    }
    println!("staged tampering: {refused} flipped bits refused");
    for (name, bad) in targeted(case) {
        let (mut chain, mut probe) = (Evm::mainnet(), Evm::new());
        let dep = staged::deploy(&mut chain, &case.key);
        staged::deploy(&mut probe, &case.key);
        let verdict = match staged::verify(&mut chain, &mut probe, dep.sessions, U256::from(1), &case.output, case.counts, BINDING, &bad) {
            Ok(_) => "ACCEPTED".to_string(),
            Err((stage, _)) => format!("refused at stage {stage}"),
        };
        println!("  staged, a lift failing only {name}: {verdict}");
    }
    let (mut chain, mut probe) = (Evm::mainnet(), Evm::new());
    let dep = staged::deploy(&mut chain, &case.key);
    staged::deploy(&mut probe, &case.key);
    println!("  staged, a state other than the session's: {}", staged::stale_state(&mut chain, &mut probe, dep.sessions, &case.output, case.counts, BINDING, &case.lift));
}

fn main() {
    let arg = |i: usize, d: usize| env::args().nth(i).map(|a| a.parse().expect("a number")).unwrap_or(d);
    let (n, chunk, rate, tables) = (arg(1, 8), arg(2, 4), arg(3, 1), arg(4, 1));
    let stop = env::args().nth(5).map(|a| a.parse::<u64>().expect("a stage"));
    let dir = cache(n, chunk, rate, tables);
    let case = match load(&dir) {
        Some(case) if env::var_os("POFSEED_WRAP_FRESH").is_none() => case,
        _ => make(n, chunk, rate, tables, &dir),
    };
    let key_path = project().join("src/wrap/WrapKey.sol");
    let before = fs::read_to_string(&key_path).ok();
    if before.as_deref() != Some(case.key.as_str()) {
        fs::write(&key_path, &case.key).expect("write the constants");
    }
    run(&case, n, chunk, rate, tables, stop);
    if let Some(before) = before
        && before != case.key
        && env::var_os("POFSEED_WRAP_KEEP").is_none()
    {
        fs::write(&key_path, before).expect("restore the constants");
    }
}

/// A number the constants' source `key` names.
fn constant(key: &str, name: &str) -> usize {
    let tag = format!("uint256 internal constant {name} = ");
    let at = key.find(&tag).unwrap_or_else(|| panic!("no constant {name}")) + tag.len();
    return key[at..at + key[at..].find(';').expect("a constant's end")].parse().expect("a number");
}

/// Lifts with one bit flipped where a single check guards: the name of the check and the lift.
fn targeted(case: &Case) -> Vec<(&'static str, Vec<u8>)> {
    let flip = |at: usize| {
        let mut bad = case.lift.clone();
        bad[at] ^= 1;
        bad
    };
    let len = case.lift.len();
    let last_rounds = 64 * constant(&case.key, "STRUCT_FINAL");
    return vec![
        ("the last opening's last equation", flip(len - 1)),
        ("a Merkle path", flip(len - last_rounds - 1)),
        ("the Fiat-Shamir gate", flip(16 * constant(&case.key, "N_IO") * constant(&case.key, "RESPONSES") + 7)),
    ];
}

fn run(case: &Case, n: usize, chunk: usize, rate: usize, tables: usize, stop: Option<u64>) {
    println!("lift of {n} responses in chunks of {chunk}, outer rate 2^-{rate}, tables' rate 2^-{tables}: {} B of calldata", case.lift.len());
    let mut evm = Evm::new();
    let (contract, name) = if stop.is_some() { ("WrapProbe.sol", "WrapProbe") } else { ("FlockWrap.sol", "FlockWrap") };
    let (address, deploy) = evm.deploy(artifact(contract, name));
    println!("{name}: runtime {} B, deployment {deploy} gas", runtime_len(contract, name));
    let call = match stop {
        Some(stop) => encode("trace(bytes,uint256,bytes,bytes,uint256)", |a| {
            a.bytes(&case.output).uint(U256::from(case.counts)).bytes(BINDING).bytes(&case.lift).uint(U256::from(stop))
        }),
        None => encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&case.output).uint(U256::from(case.counts)).bytes(BINDING).bytes(&case.lift)),
    };
    let t = Instant::now();
    let out = evm.call(address, call);
    println!("ran in {:.2} s: success {}, gas {} (execution {}, calldata and base {})", t.elapsed().as_secs_f64(), out.success, out.gas, out.execution(), out.intrinsic);
    if !out.success {
        println!("  revert data: {}", hex::encode(&out.output[..out.output.len().min(68)]));
    }
    let mut last: Option<u64> = Some(evm.gas_limit() - out.intrinsic);
    let mut ok = true;
    for (topics, data) in &out.logs {
        let id = U256::from_be_bytes(topics[1]).to::<u32>();
        let gas = U256::from_be_bytes::<32>(data[..32].try_into().unwrap()).to::<u64>();
        let state: [u8; 32] = data[32..64].try_into().unwrap();
        let memory = U256::from_be_bytes::<32>(data[64..96].try_into().unwrap()).to::<u64>();
        let expected = case.marks.iter().find(|(m, _)| *m == id).map(|(_, s)| *s);
        let verdict = match expected {
            Some(e) if e == state => "✓",
            Some(_) => {
                ok = false;
                "✗ DIFFERS from the mirror"
            }
            None => "",
        };
        println!("  stage {id:>3}: {:>12} gas, {:>4} KB of memory {verdict}", last.map_or(0, |l| l - gas), memory / 1024);
        last = Some(gas);
    }
    assert!(ok, "a stage's transcript differs from the mirror's");
    if stop.is_none() {
        assert!(out.success, "the contract refused the lift");
        staged_run(case);
        let mut refused = 0;
        for at in (0..case.lift.len()).step_by(case.lift.len() / 23 + 1) {
            let mut bad = case.lift.clone();
            bad[at] ^= 1;
            let call = encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&case.output).uint(U256::from(case.counts)).bytes(BINDING).bytes(&bad));
            if evm.simulate(address, call).success {
                println!("  a flipped bit at byte {at} is ACCEPTED");
            } else {
                refused += 1;
            }
        }
        println!("tampering: {refused} flipped bits refused");
        let other_split = (case.counts - 8) & 0xffff | ((case.counts >> 32) + 1) << 32;
        let call = encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&case.output).uint(U256::from(other_split)).bytes(BINDING).bytes(&case.lift));
        println!("  another split of the output's word counts: {}", if evm.simulate(address, call).success { "ACCEPTED" } else { "refused" });
        for (name, bad) in targeted(case) {
            let call = encode("verify(bytes,uint256,bytes,bytes)", |a| a.bytes(&case.output).uint(U256::from(case.counts)).bytes(BINDING).bytes(&bad));
            let verdict = if evm.simulate(address, call).success { "ACCEPTED" } else { "refused" };
            println!("  a lift failing only {name}: {verdict}");
        }
    }
}
