// SPDX-License-Identifier: LGPL-3.0-or-later

//! Verification of a wrapped lift in transactions that each fit mainnet's gas cap: the stage
//! contracts, their deployment, and a driver that advances a session one capped transaction at a
//! time, sending each stage exactly the bytes it reads.

use std::path::Path;

use revm::primitives::{Address, U256};

use crate::evm::{CODE_CAP, Evm, artifact_at, build, encode, project, runtime_len_at};

/// The stage contracts, with the table each reads from a data contract, if any.
const STAGES: [(&str, Option<&str>); 7] = [
    ("WrapStageA", Some("FIXED")),
    ("WrapStageB", Some("ELEM_DATA")),
    ("WrapStageC", Some("RUNS")),
    ("WrapStageD", Some("SUBSPACE")),
    ("WrapStageE", None),
    ("WrapStageF", Some("SUBSPACE")),
    ("WrapStageG", Some("SUBSPACE")),
];

/// The stage after the last.
const DONE: u64 = 8;

/// What each stage does.
pub fn stage_name(stage: u64) -> &'static str {
    return match stage {
        1 => "gate, binding, zerocheck, lincheck, wiring",
        2 => "element class, ring switches, assist sumchecks, claim weights",
        3 => "layout equation",
        4 => "outer opening",
        5 => "table folds and sumchecks, bit claims' batching",
        6 => "bit claim's conjugates, tables' opening",
        7 => "tables' opening's last equation",
        _ => "?",
    };
}

/// A deployed staged verifier.
pub struct Deployment {
    /// The session contract.
    pub sessions: Address,
    /// Each deployed contract's name, runtime size and deployment gas.
    pub contracts: Vec<(String, usize, u64)>,
}

/// One transaction of a staged verification.
#[derive(Clone, Debug)]
pub struct Tx {
    /// The stage it ran.
    pub stage: u64,
    /// Its gas, intrinsic gas included.
    pub gas: u64,
    /// Bytes of the lift's encoding it carried.
    pub data: usize,
    /// Bytes of state it carried.
    pub state: usize,
}

fn address_word(a: Address) -> Vec<u8> {
    let mut w = vec![0u8; 12];
    w.extend_from_slice(a.as_slice());
    return w;
}

/// The bytes of the table `name` in the generated constants' source `key`.
fn table(key: &str, name: &str) -> Vec<u8> {
    let tag = format!("bytes internal constant {name} = hex\"");
    let at = key.find(&tag).unwrap_or_else(|| panic!("no table {name}")) + tag.len();
    let end = at + key[at..].find('"').expect("table end");
    return hex::decode(&key[at..end]).expect("table hex");
}

/// Creation code of a contract holding `data` after a leading `STOP`.
fn data_contract(data: &[u8]) -> Vec<u8> {
    let n = data.len() + 1;
    let mut code = vec![0x61, (n >> 8) as u8, n as u8, 0x80, 0x60, 0x0c, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00];
    code.extend_from_slice(data);
    return code;
}

/// Deploys the staged verifier whose constants' source is `key`, every contract under the
/// code-size limit.
pub fn deploy(evm: &mut Evm, key: &str) -> Deployment {
    build();
    let deployment = deploy_at(evm, key, &project());
    for (name, size, _) in &deployment.contracts {
        assert!(*size <= CODE_CAP, "{name} is {size} bytes");
    }
    return deployment;
}

/// Deploys the staged verifier whose constants' source is `key` from the built Foundry project at
/// `dir`.
pub fn deploy_at(evm: &mut Evm, key: &str, dir: &Path) -> Deployment {
    let mut contracts = Vec::new();
    let mut stores: Vec<(&str, Address)> = Vec::new();
    let mut targets = Vec::new();
    for (name, data) in STAGES {
        let mut code = artifact_at(dir, "WrapStages.sol", name);
        if let Some(data) = data {
            let store = match stores.iter().find(|(d, _)| *d == data) {
                Some(&(_, at)) => at,
                None => {
                    let bytes = table(key, data);
                    let (at, gas) = evm.deploy(data_contract(&bytes));
                    contracts.push((format!("table {data}"), bytes.len() + 1, gas));
                    stores.push((data, at));
                    at
                }
            };
            code.extend(address_word(store));
        }
        let (at, gas) = evm.deploy(code);
        let size = runtime_len_at(dir, "WrapStages.sol", name);
        contracts.push((name.to_string(), size, gas));
        targets.push(at);
    }
    let mut code = artifact_at(dir, "WrapSessions.sol", "WrapSessions");
    code.extend(address_word(targets[0]));
    code.extend(U256::from(0x40).to_be_bytes::<32>());
    code.extend(U256::from(targets.len() - 1).to_be_bytes::<32>());
    for t in &targets[1..] {
        code.extend(address_word(*t));
    }
    let (sessions, gas) = evm.deploy(code);
    contracts.push(("WrapSessions".to_string(), runtime_len_at(dir, "WrapSessions.sol", "WrapSessions"), gas));
    return Deployment { sessions, contracts };
}

/// The state a call returned: the bytes, the stage it is at, the statement's digest and the cursor.
fn state_of(output: &[u8]) -> (Vec<u8>, u64, [u8; 32], usize) {
    let word = |b: &[u8], i: usize| U256::from_be_slice(&b[32 * i..32 * i + 32]);
    let len = word(output, 1).to::<usize>();
    let state = output[64..64 + len].to_vec();
    let stage = word(&state, 1).to::<u64>();
    let digest: [u8; 32] = state[64..96].try_into().expect("a digest");
    let scalars = 32 + word(&state, 3).to::<usize>();
    let cursor = word(&state[scalars..], 1).to::<usize>();
    return (state, stage, digest, cursor);
}

fn start(salt: U256, output: &[u8], counts: u64, binding: &[u8], data: &[u8]) -> Vec<u8> {
    return encode("start(bytes32,bytes,uint256,bytes,bytes)", |a| a.uint(salt).bytes(output).uint(U256::from(counts)).bytes(binding).bytes(data));
}

fn advance(salt: U256, state: &[u8], data: &[u8]) -> Vec<u8> {
    return encode("advance(bytes32,bytes,bytes)", |a| a.uint(salt).bytes(state).bytes(data));
}

/// Verifies the lift `lift` against `output`, with its word counts, under `binding`, in session
/// `salt` of the staged verifier at `sessions`, which `chain` and `probe` both hold: `probe`, which
/// caps nothing, learns how much of the lift each stage reads, and `chain` runs every transaction.
/// Returns the transactions and the accepted digest, or the stage that refused with its revert
/// data.
pub fn verify(
    chain: &mut Evm,
    probe: &mut Evm,
    sessions: Address,
    salt: U256,
    output: &[u8],
    counts: u64,
    binding: &[u8],
    lift: &[u8],
) -> Result<(Vec<Tx>, [u8; 32]), (u64, Vec<u8>)> {
    let mut txs = Vec::new();
    let learned = probe.simulate(sessions, start(salt, output, counts, binding, lift));
    if !learned.success {
        return Err((1, learned.output));
    }
    let (_, _, _, mut cursor) = state_of(&learned.output);
    let call = start(salt, output, counts, binding, &lift[..cursor]);
    assert!(probe.call(sessions, call.clone()).success, "the probe follows the chain");
    let out = chain.call(sessions, call);
    if !out.success {
        return Err((1, out.output));
    }
    let (mut state, mut stage, mut digest, at) = state_of(&out.output);
    assert_eq!(at, cursor, "a stage reads the same bytes of a longer stream");
    txs.push(Tx { stage: 1, gas: out.gas, data: cursor, state: 0 });
    while stage != DONE {
        let learned = probe.simulate(sessions, advance(salt, &state, &lift[cursor..]));
        if !learned.success {
            return Err((stage, learned.output));
        }
        let (_, _, _, next) = state_of(&learned.output);
        let call = advance(salt, &state, &lift[cursor..next]);
        assert!(probe.call(sessions, call.clone()).success, "the probe follows the chain");
        let out = chain.call(sessions, call);
        if !out.success {
            return Err((stage, out.output));
        }
        txs.push(Tx { stage, gas: out.gas, data: next - cursor, state: state.len() });
        (state, stage, digest, cursor) = state_of(&out.output);
        assert_eq!(cursor, next, "a stage reads the same bytes of a longer stream");
    }
    assert_eq!(cursor, lift.len(), "the stages read the whole lift");
    return Ok((txs, digest));
}

/// Whether the staged verifier at `sessions` has accepted the statement with digest `digest`.
pub fn accepted(evm: &mut Evm, sessions: Address, digest: &[u8; 32]) -> bool {
    let out = evm.simulate(sessions, encode("accepted(bytes32)", |a| a.uint(U256::from_be_bytes(*digest))));
    return out.success && U256::from_be_slice(&out.output) == U256::from(1);
}

/// Starts a session on `lift`, then advances it with its state under another digest, which no
/// stage reads before the last, and with the state of another caller's session; says what the
/// session contract did with each.
pub fn stale_state(chain: &mut Evm, probe: &mut Evm, sessions: Address, output: &[u8], counts: u64, binding: &[u8], lift: &[u8]) -> String {
    let salt = U256::from(7);
    let learned = probe.simulate(sessions, start(salt, output, counts, binding, lift));
    let (_, _, _, cursor) = state_of(&learned.output);
    let call = start(salt, output, counts, binding, &lift[..cursor]);
    assert!(probe.call(sessions, call.clone()).success, "the probe follows the chain");
    let out = chain.call(sessions, call);
    assert!(out.success, "the first stage accepts");
    let (state, _, _, _) = state_of(&out.output);
    let learned = probe.simulate(sessions, advance(salt, &state, &lift[cursor..]));
    assert!(learned.success, "the second stage accepts");
    let (_, _, _, next) = state_of(&learned.output);
    let data = &lift[cursor..next];
    assert!(chain.simulate(sessions, advance(salt, &state, data)).success, "the session's own state advances it");
    let mut bad = state.clone();
    bad[95] ^= 1;
    let tampered = chain.simulate(sessions, advance(salt, &bad, data));
    let other = chain.simulate(sessions, advance(U256::from(8), &state, data));
    let verdict = |o: &crate::evm::Outcome| if o.success { "ACCEPTED" } else { "refused" };
    return format!("a state under another digest {}, another session's state {}", verdict(&tampered), verdict(&other));
}
