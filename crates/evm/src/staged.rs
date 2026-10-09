// SPDX-License-Identifier: LGPL-3.0-or-later

//! Direct verification of a lift in transactions that each fit mainnet's gas cap: the staged
//! contracts, their deployment, and a driver that advances a session one capped transaction at a
//! time, choosing each transaction's item range by simulating it.

use pofseed_flock_lift::matrix::MatrixCommitment;
use pofseed_flock_lift_block::program::Program;
use revm::primitives::{Address, U256, keccak256};

use crate::evm::{CODE_CAP, Evm, Outcome, TX_CAP, artifact, encode, project, runtime_len};

/// The contracts of the staged verifier, with the stages each runs.
pub const STAGE_CONTRACTS: [(&str, &[u64]); 7] = [
    ("LiftStages", &[1, 2]),
    ("LiftTailStages", &[3, 4, 5]),
    ("OpeningStages", &[20, 21, 22, 23, 24]),
    ("RingSwitchStages", &[40]),
    ("ConsistencyStages", &[41]),
    ("MatrixStages", &[50, 51, 52, 53, 54, 55, 56]),
    ("StructuredStages", &[70]),
];

/// Stage numbers, as `staged/Staged.sol` has them.
pub const LIFT_DONE: u64 = 19;
/// The matrix session's last stage.
pub const MATRIX_DONE: u64 = 69;

/// The name of stage `stage`.
pub fn stage_name(stage: u64) -> &'static str {
    return match stage {
        1 => "published words",
        2 => "chunk PIOP",
        3 => "published-word claim",
        4 => "chunk final check",
        5 => "Fiat-Shamir gate",
        20 => "ring switches",
        21 => "Ligerito rows",
        22 => "Ligerito level",
        23 => "Ligerito final message",
        24 => "out-of-domain residual",
        40 => "ring-switch residual",
        41 => "consistency residual",
        50 => "matrix cap",
        51 => "matrix main sumcheck",
        52 => "matrix main check",
        53 => "matrix counts",
        54 => "matrix prefix counts",
        55 => "matrix count sumcheck",
        56 => "matrix final check",
        70 => "structured parts",
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

fn word(v: U256) -> Vec<u8> {
    return v.to_be_bytes::<32>().to_vec();
}

fn address_word(a: Address) -> Vec<u8> {
    let mut w = vec![0u8; 12];
    w.extend_from_slice(a.as_slice());
    return w;
}

/// `Constants.SUBSPACE`, as the generated source holds it.
fn subspace() -> Vec<u8> {
    let src = std::fs::read_to_string(project().join("src/Constants.sol")).expect("constants source");
    let at = src.find("SUBSPACE = hex\"").expect("subspace table") + "SUBSPACE = hex\"".len();
    let end = at + src[at..].find('"').expect("table end");
    return hex::decode(&src[at..end]).expect("table hex");
}

/// Creation code of a contract holding `data` after a leading `STOP`.
fn data_contract(data: &[u8]) -> Vec<u8> {
    let n = data.len() + 1;
    let mut code = vec![0x61, (n >> 8) as u8, n as u8, 0x80, 0x60, 0x0c, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00];
    code.extend_from_slice(data);
    return code;
}

fn deploy_one(evm: &mut Evm, out: &mut Vec<(String, usize, u64)>, name: &str, args: &[Vec<u8>]) -> Address {
    let mut code = artifact(&format!("{name}.sol"), name);
    for a in args {
        code.extend_from_slice(a);
    }
    let (at, gas) = evm.deploy(code);
    let size = runtime_len(&format!("{name}.sol"), name);
    assert!(size <= CODE_CAP, "{name} is {size} bytes");
    out.push((name.to_string(), size, gas));
    return at;
}

/// Deploys the staged verifier of the statement with circuit fingerprint `fingerprint`, chain code
/// `chain_code` and child index `index`, whose expected output has the packed word counts `counts`,
/// lifted with at least `min_responses` responses, and of the entry commitment `key` of `program`.
pub fn deploy(
    evm: &mut Evm,
    fingerprint: &[u8; 32],
    chain_code: &[u8],
    index: u32,
    min_responses: usize,
    counts: U256,
    program: &Program,
    key: &MatrixCommitment,
    slim: bool,
) -> Deployment {
    let mut contracts = Vec::new();
    let table = subspace();
    let (store, store_gas) = evm.deploy(data_contract(&table));
    contracts.push(("subspace table".to_string(), table.len() + 1, store_gas));
    let g = program.geometry();
    let slim_word = word(U256::from(slim as u8));
    let mut routes = Vec::new();
    let mut lift = Address::ZERO;
    let mut matrix = Address::ZERO;
    for (name, stages) in STAGE_CONTRACTS {
        let args: Vec<Vec<u8>> = match name {
            "LiftStages" => vec![
                fingerprint.to_vec(),
                chain_code.to_vec(),
                word(U256::from(index)),
                word(U256::from(min_responses)),
                word(counts),
                slim_word.clone(),
            ],
            "ConsistencyStages" => vec![address_word(store)],
            "MatrixStages" => vec![
                keccak256(key.commitment.cap.concat()).0.to_vec(),
                slim_word.clone(),
                word(U256::from(g.head_subs())),
                word(U256::from(g.keccak_subs())),
            ],
            _ => vec![],
        };
        let at = deploy_one(evm, &mut contracts, name, &args);
        match name {
            "LiftStages" => lift = at,
            "MatrixStages" => matrix = at,
            _ => {}
        }
        for &s in stages {
            routes.push((s, at));
        }
    }
    let stages: Vec<U256> = routes.iter().map(|&(s, _)| U256::from(s)).collect();
    let targets: Vec<U256> = routes.iter().map(|&(_, a)| U256::from_be_slice(&address_word(a))).collect();
    let args = encode("x()", |a| {
        a.uint(U256::from_be_slice(&address_word(lift)))
            .uint(U256::from_be_slice(&address_word(matrix)))
            .uints(&stages)
            .uints(&targets)
    });
    let sessions = deploy_one(evm, &mut contracts, "FlockSessions", &[args[4..].to_vec()]);
    return Deployment { sessions, contracts };
}

/// One transaction of a staged verification.
#[derive(Clone, Debug)]
pub struct Tx {
    /// The stage it ran.
    pub stage: u64,
    /// The items it ran.
    pub items: (u64, u64),
    /// Gas used, calldata included.
    pub gas: u64,
    /// Intrinsic gas.
    pub intrinsic: u64,
    /// Bytes of state it carried in.
    pub state: usize,
    /// Bytes of proof it carried in.
    pub data: usize,
}

/// A stream request: `[source, base, unit, length]`.
#[derive(Clone, Copy, Debug)]
struct Stream {
    source: usize,
    base: usize,
    unit: usize,
    length: usize,
}

/// What a stage asks of its next call.
#[derive(Clone, Debug)]
struct Want {
    streams: Vec<Stream>,
    pos: usize,
    cursor: u64,
    items: u64,
}

fn words(out: &[u8], at: usize) -> U256 {
    return U256::from_be_slice(&out[at..at + 32]);
}

/// The `(bytes, uint256[])` a stage call returns, from the output `out` whose dynamic heads sit at
/// `heads`.
fn decode(out: &[u8], heads: usize) -> (Vec<u8>, Want) {
    let so = words(out, heads).to::<usize>();
    let slen = words(out, so).to::<usize>();
    let state = out[so + 32..so + 32 + slen].to_vec();
    let wo = words(out, heads + 32).to::<usize>();
    let wlen = words(out, wo).to::<usize>();
    let w: Vec<usize> = (0..wlen).map(|i| words(out, wo + 32 + 32 * i).to::<usize>()).collect();
    let mut streams = Vec::new();
    let mut want = Want { streams: Vec::new(), pos: 0, cursor: 0, items: 0 };
    for q in w.chunks(4) {
        if q[0] == 99 {
            want.pos = q[1];
            want.cursor = q[2] as u64;
            want.items = q[3] as u64;
        } else {
            streams.push(Stream { source: q[0], base: q[1], unit: q[2], length: q[3] });
        }
    }
    want.streams = streams;
    return (state, want);
}

fn stage_of(state: &[u8]) -> u64 {
    return words(state, 0).to::<u64>();
}

/// The window a sequential stage is offered before its read is measured.
const WINDOW: usize = 1 << 15;

fn gather(want: &Want, sources: &[&[u8]], from: u64, to: u64, windows: &[usize]) -> Vec<u8> {
    let mut data = Vec::new();
    for (i, s) in want.streams.iter().enumerate() {
        let src = sources[s.source];
        let (a, b) = if s.unit > 0 {
            (s.base + s.unit * from as usize, s.base + s.unit * to as usize)
        } else if s.length > 0 {
            (s.base, s.base + s.length)
        } else {
            (s.base, (s.base + windows[i]).min(src.len()))
        };
        data.extend_from_slice(&src[a..b]);
    }
    return data;
}

fn advance_call(salt: U256, state: &[u8], upto: u64, data: &[u8]) -> Vec<u8> {
    return encode("advance(bytes32,bytes,uint256,bytes)", |a| {
        a.uint(salt).bytes(state).uint(U256::from(upto)).bytes(data)
    });
}

fn fits(out: &Outcome) -> bool {
    return out.success && out.gas <= TX_CAP;
}

/// Advances the caller's session `salt`, now at `state` and asking `want`, to its end, reading the
/// byte sources `sources` (the proof, then the expected output and the binding), each transaction
/// sized to fit the gas cap.
fn drive(
    evm: &mut Evm,
    sessions: Address,
    salt: U256,
    mut state: Vec<u8>,
    mut want: Want,
    sources: &[&[u8]],
) -> Result<Vec<Tx>, Refusal> {
    let mut txs = Vec::new();
    loop {
        let stage = stage_of(&state);
        let (cursor, items) = (want.cursor, want.items);
        let mut windows: Vec<usize> = want.streams.iter().map(|_| WINDOW).collect();
        let sequential = want.streams.iter().any(|s| s.unit == 0 && s.length == 0);
        let try_upto = |evm: &mut Evm, windows: &[usize], upto: u64| -> (Outcome, Vec<u8>) {
            let data = gather(&want, sources, cursor, upto, windows);
            let out = evm.simulate(sessions, advance_call(salt, &state, upto, &data));
            return (out, data);
        };
        if sequential {
            let (probe, _) = try_upto(evm, &windows, cursor + 1);
            if !probe.success {
                return Err(Refusal { stage, item: cursor, output: probe.output });
            }
            let (_, next_want) = decode(&probe.output, 0);
            for (i, s) in want.streams.iter().enumerate() {
                if s.unit == 0 && s.length == 0 {
                    windows[i] = next_want.pos - s.base;
                }
            }
        }
        let (mut lo, mut hi) = (cursor + 1, items);
        let (first, _) = try_upto(evm, &windows, lo);
        if !first.success {
            return Err(Refusal { stage, item: cursor, output: first.output });
        }
        assert!(first.gas <= TX_CAP, "stage {stage} ({}) item {cursor} needs {} gas", stage_name(stage), first.gas);
        while lo < hi {
            let mid = (lo + hi + 1) / 2;
            let (out, _) = try_upto(evm, &windows, mid);
            if fits(&out) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        let (_, data) = try_upto(evm, &windows, lo);
        let call = advance_call(salt, &state, lo, &data);
        let out = evm.call(sessions, call);
        assert!(fits(&out), "stage {stage} committed call failed");
        txs.push(Tx {
            stage,
            items: (cursor, lo),
            gas: out.gas,
            intrinsic: out.intrinsic,
            state: state.len(),
            data: data.len(),
        });
        let (next, next_want) = decode(&out.output, 0);
        let next_stage = stage_of(&next);
        if next_stage == LIFT_DONE || next_stage == MATRIX_DONE {
            return Ok(txs);
        }
        state = next;
        want = next_want;
    }
}

/// A stage's refusal: the stage, the item it refused at and its revert data.
#[derive(Debug)]
pub struct Refusal {
    /// The stage.
    pub stage: u64,
    /// The first item of the refused call.
    pub item: u64,
    /// The revert data.
    pub output: Vec<u8>,
}

/// The outcome of a staged session.
pub struct Session {
    /// Its transactions, the opening one first.
    pub txs: Vec<Tx>,
}

/// Verifies a lift of `n` responses in chunks of `chunk` in capped transactions, from the
/// caller's session `salt`.
pub fn lift(
    evm: &mut Evm,
    sessions: Address,
    salt: U256,
    output: &[u8],
    counts: U256,
    binding: &[u8],
    proof: &[u8],
    n: usize,
    chunk: usize,
) -> Result<Session, Refusal> {
    let call = encode("startLift(bytes32,bytes,uint256,bytes,uint256,uint256)", |a| {
        a.uint(salt).bytes(output).uint(counts).bytes(binding).uint(U256::from(n)).uint(U256::from(chunk))
    });
    let len = call.len();
    let out = evm.call(sessions, call);
    if !fits(&out) {
        return Err(Refusal { stage: 0, item: 0, output: out.output });
    }
    let (state, want) = decode(&out.output, 32);
    let mut txs = vec![Tx { stage: 0, items: (0, 1), gas: out.gas, intrinsic: out.intrinsic, state: 0, data: len }];
    txs.extend(drive(evm, sessions, salt, state, want, &[proof, output, binding])?);
    return Ok(Session { txs });
}

/// Opens a matrix session on `claims` for the lift with statement digest `digest`, returning the
/// call's outcome.
pub fn start_matrix(evm: &mut Evm, sessions: Address, salt: U256, digest: &[u8; 32], claims: &[U256]) -> Outcome {
    let call = encode("startMatrix(bytes32,bytes32,uint256[])", |a| {
        a.uint(salt).uint(U256::from_be_bytes(*digest)).uints(claims)
    });
    return evm.call(sessions, call);
}

/// Verifies the matrix proof `proof` of the lift with statement digest `digest` and packed claims
/// `claims`, in capped transactions from the caller's session `salt`.
pub fn matrix(
    evm: &mut Evm,
    sessions: Address,
    salt: U256,
    digest: &[u8; 32],
    claims: &[U256],
    proof: &[u8],
) -> Result<Session, Refusal> {
    let out = start_matrix(evm, sessions, salt, digest, claims);
    if !fits(&out) {
        return Err(Refusal { stage: 50, item: 0, output: out.output });
    }
    let (state, want) = decode(&out.output, 32);
    let mut txs = vec![Tx {
        stage: 0,
        items: (0, 1),
        gas: out.gas,
        intrinsic: out.intrinsic,
        state: 0,
        data: 32 * claims.len(),
    }];
    txs.extend(drive(evm, sessions, salt, state, want, &[proof])?);
    return Ok(Session { txs });
}

/// A raw call advancing the caller's session `salt` from `state` up to `upto`, reading `data`.
pub fn advance(evm: &mut Evm, sessions: Address, salt: U256, state: &[u8], upto: u64, data: &[u8]) -> Outcome {
    return evm.call(sessions, advance_call(salt, state, upto, data));
}

/// Opens the caller's lift session `salt`, returning the call's outcome and the first state.
pub fn start_lift(
    evm: &mut Evm,
    sessions: Address,
    salt: U256,
    output: &[u8],
    counts: U256,
    binding: &[u8],
    n: usize,
    chunk: usize,
) -> (Outcome, Vec<u8>) {
    let call = encode("startLift(bytes32,bytes,uint256,bytes,uint256,uint256)", |a| {
        a.uint(salt).bytes(output).uint(counts).bytes(binding).uint(U256::from(n)).uint(U256::from(chunk))
    });
    let out = evm.call(sessions, call);
    let state = if out.success { decode(&out.output, 32).0 } else { Vec::new() };
    return (out, state);
}

/// Whether the session contract has recorded the lift with digest `digest`, and the hash of its
/// claims.
pub fn recorded(evm: &mut Evm, sessions: Address, digest: &[u8; 32]) -> (U256, bool) {
    let claims = evm.simulate(sessions, encode("liftClaims(bytes32)", |a| a.uint(U256::from_be_bytes(*digest))));
    let accepted = evm.simulate(sessions, encode("accepted(bytes32)", |a| a.uint(U256::from_be_bytes(*digest))));
    return (U256::from_be_bytes(claims.word(0)), accepted.word(0)[31] == 1);
}
