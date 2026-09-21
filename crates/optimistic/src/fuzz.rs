// SPDX-License-Identifier: LGPL-3.0-or-later

//! Differential fuzzing of the one-step contract against revm on random programs: every step of
//! every program, including the steps that halt it, must lead the contract to the state revm
//! reached, or to rejection where the machine departs from revm.

use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

use pofseed_flock_lift_evm::evm::{artifact, encode};
use revm::primitives::{Address, B256, U256, keccak256};

use crate::{
    deploy::{onestep_args, step_calldata},
    machine::Machine,
    merkle::{root as tree_root, words_of},
    trace::{Capture, Captured},
    vm::{ACCEPTED, BODY_DEPTH, CallData, Committed, Ctx, MEM_DEPTH, REJECTED, StepWitness, start_hash, supported, terminal},
};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        return self.0;
    }

    fn below(&mut self, n: u64) -> u64 {
        return self.next() % n;
    }

    fn word(&mut self) -> [u8; 32] {
        let mut w = [0u8; 32];
        for chunk in w.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        return w;
    }
}

fn push(code: &mut Vec<u8>, v: &[u8]) {
    let v: Vec<u8> = v.iter().copied().skip_while(|&b| b == 0).collect();
    if v.is_empty() {
        code.push(0x5f);
    } else {
        code.push(0x5f + v.len() as u8);
        code.extend_from_slice(&v);
    }
}

/// A random program: values pushed, then a mix of operations, jumps to marked destinations, and
/// occasionally an opcode outside the machine or a huge memory offset.
fn program(r: &mut Rng) -> Vec<u8> {
    let mut code = vec![0x5f];
    for _ in 0..16 {
        let v = match r.below(4) {
            0 => r.word().to_vec(),
            1 => (r.below(256) as u16).to_be_bytes().to_vec(),
            2 => r.word()[..1 + r.below(31) as usize].to_vec(),
            _ => (r.below(4096) as u16).to_be_bytes().to_vec(),
        };
        push(&mut code, &v);
    }
    let ops: &[u8] = &[
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x20, 0x30, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3d,
        0x3e, 0x46, 0x50, 0x51, 0x52, 0x53, 0x58, 0x59, 0x5a, 0x5b, 0x5e, 0x80, 0x81, 0x82, 0x83, 0x8f, 0x90, 0x91, 0x92,
        0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4,
    ];
    let len = 20 + r.below(120) as usize;
    let mut dests = Vec::new();
    for _ in 0..len {
        match r.below(20) {
            0..=6 => {
                let v = match r.below(6) {
                    0 => r.word().to_vec(),
                    1 => vec![r.below(2) as u8],
                    2 => (r.below(64) as u16).to_be_bytes().to_vec(),
                    3 => (r.below(2048) as u16).to_be_bytes().to_vec(),
                    4 => (r.below(1 << 20) as u32).to_be_bytes().to_vec(),
                    _ => (r.below(300) as u16).to_be_bytes().to_vec(),
                };
                push(&mut code, &v);
            }
            7..=15 => code.push(ops[r.below(ops.len() as u64) as usize]),
            16 => {
                dests.push(code.len());
                code.push(0x5b);
            }
            17 => {
                let pos = code.len();
                code.extend_from_slice(&[0x61, 0, 0, if r.below(2) == 0 { 0x56 } else { 0x57 }]);
                dests.push(usize::MAX - pos);
            }
            18 => match r.below(8) {
                0 => code.push([0x54, 0x55, 0xf1, 0x31, 0x40, 0x5c, 0x0c, 0xef][r.below(8) as usize]),
                1 => {
                    push(&mut code, &[0x08, 0x00, 0x00, 0x00]);
                    code.push(0x51);
                }
                2 | 3 => {
                    push(&mut code, &(r.below(64) as u16).to_be_bytes());
                    push(&mut code, &(r.below(128) as u16).to_be_bytes());
                    push(&mut code, &(r.below(1 << 12) as u16).to_be_bytes());
                    push(&mut code, &(r.below(512) as u16).to_be_bytes());
                    push(&mut code, &[if r.below(4) == 0 { 0x04 } else { 0x02 }]);
                    if r.below(3) == 0 {
                        push(&mut code, &(r.below(200) as u16).to_be_bytes());
                    } else {
                        code.push(0x5a);
                    }
                    code.push(0xfa);
                    if r.below(2) == 0 {
                        push(&mut code, &(r.below(40) as u16).to_be_bytes());
                        push(&mut code, &(r.below(40) as u16).to_be_bytes());
                        push(&mut code, &(r.below(128) as u16).to_be_bytes());
                        code.push(0x3e);
                    }
                }
                4 => code.push(0xfe),
                5 => code.push(0xfd),
                6 => code.push(0x00),
                _ => {
                    if r.below(2) == 0 {
                        push(&mut code, &[0x20]);
                        push(&mut code, &[0x00]);
                        code.push(0x52);
                        push(&mut code, &[0x01]);
                        push(&mut code, &[0x20]);
                        code.push(0x52);
                        push(&mut code, &r.word());
                        push(&mut code, &[0x40]);
                        code.push(0x52);
                        push(&mut code, &[0x60]);
                        push(&mut code, &[0x00]);
                    }
                    code.push(0xf3);
                }
            },
            _ => {
                let n = 1 + r.below(8) as usize;
                code.push(0x60 + n as u8 - 1);
                for _ in 0..n {
                    code.push(if r.below(3) == 0 { 0x5b } else { r.below(256) as u8 });
                }
            }
        }
    }
    let targets: Vec<usize> = dests.iter().copied().filter(|&d| d < usize::MAX / 2).collect();
    for d in dests.iter().copied().filter(|&d| d >= usize::MAX / 2) {
        let pos = usize::MAX - d;
        let t = if targets.is_empty() || r.below(8) == 0 { r.below(code.len() as u64 + 2) as usize } else { targets[r.below(targets.len() as u64) as usize] };
        code[pos + 1..pos + 3].copy_from_slice(&(t as u16).to_be_bytes());
    }
    return code;
}

/// What a fuzzing campaign checked.
#[derive(Clone, Debug, Default)]
pub struct FuzzReport {
    /// Programs run.
    pub programs: usize,
    /// Steps checked.
    pub steps: usize,
    /// Of them, steps the machine continues from.
    pub continuing: usize,
    /// Of them, steps the machine rejects at.
    pub rejecting: usize,
    /// Distinct opcodes checked.
    pub opcodes: usize,
    /// Steps where the contract disagreed.
    pub mismatches: usize,
}

/// Checks the one-step contract against revm on `programs` random programs drawn from `seed`.
pub fn run(programs: usize, seed: u64, verbose: bool) -> FuzzReport {
    let mut r = Rng(seed);
    let mut machine = Machine::new(false);
    let (store, _) = machine.deploy(artifact("Store.sol", "Store"));
    let mut steps_checked = 0usize;
    let mut kinds = [0usize; 3];
    let mut ops_seen = BTreeSet::new();
    let mut failures = 0;
    for p in 0..programs {
        let code = program(&mut r);
        let mut init = vec![0x61, 0, 0, 0x80, 0x60, 0x0c, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3];
        init[1..3].copy_from_slice(&(code.len() as u16).to_be_bytes());
        init.extend_from_slice(&code);
        let (target, _) = machine.deploy(init);
        let res = machine.call(store, encode("put(bytes)", |a| a.bytes(&code)));
        let chunk = Address::from_slice(&res.output[12..32]);
        let args = onestep_args((&[chunk], code.len()), (&[chunk], code.len()), [target, target], [0; 7]);
        let mut oc = artifact("OneStep.sol", "OneStep");
        oc.extend_from_slice(&args);
        let (onestep, _) = machine.deploy(oc);
        machine.call(onestep, encode("buildJumps(uint256)", |a| a.uint(U256::ZERO)));
        machine.call(onestep, encode("buildJumps(uint256)", |a| a.uint(U256::from(1))));
        let words = r.below(40) as usize;
        let mut data = r.word()[..4].to_vec();
        for _ in 0..words {
            data.extend_from_slice(&r.word());
        }
        let prefix = if words == 0 { 0 } else { r.below(words as u64 + 1) as usize };
        let call = r.below(2) as usize;
        let matrix: Vec<u8> = (0..r.below(200)).map(|_| r.below(256) as u8).collect();
        let tail = if call == 0 {
            [r.word(), tree_root(&words_of(&matrix), BODY_DEPTH).0, U256::from(matrix.len()).to_be_bytes()]
        } else {
            [r.word(), [0u8; 32], [0u8; 32]]
        };
        let ctx = Ctx {
            call,
            calldata: CallData::new(data.clone(), prefix, None),
            tail,
        };
        let cases: Arc<Mutex<Vec<(Vec<u8>, B256, B256, u8)>>> = Arc::new(Mutex::new(Vec::new()));
        let sink = cases.clone();
        let (ctx_c, code_c, matrix_c) = (ctx.clone(), code.clone(), matrix.clone());
        let limit = 32usize << MEM_DEPTH;
        let on = Box::new(move |cap: Captured| {
            if cap.pre.memory.len() > limit {
                return;
            }
            let pre = Committed::new(&cap.pre);
            let op = code_c.get(cap.pre.pc).copied().unwrap_or(0);
            let (witness, output) = StepWitness::new(&pre, &ctx_c, &code_c).build();
            let s = &cap.pre.stack;
            let foreign_call = op == 0xfa && s.len() >= 6 && s[s.len() - 2] != U256::from(2);
            let after = if !supported(op) || foreign_call {
                terminal(REJECTED)
            } else {
                match (&cap.post, &output) {
                    (Some(post), None) if post.memory.len() > limit => terminal(REJECTED),
                    (Some(post), None) => Committed::new(post).hash(&ctx_c),
                    (None, Some(out)) if ctx_c.call == 1 => {
                        terminal(if out.len() == 32 && U256::from_be_slice(out) == U256::from(1) { ACCEPTED } else { REJECTED })
                    }
                    (None, Some(out)) => {
                        let well_formed = out.len() >= 64
                            && U256::from_be_slice(&out[..32]) == U256::from(32)
                            && U256::from_be_slice(&out[32..64]) <= U256::from((out.len() - 64) / 32)
                            && out.len() == 64 + 32 * U256::from_be_slice(&out[32..64]).to::<usize>();
                        if well_formed {
                            let claims: Vec<U256> = out[64..].chunks(32).map(U256::from_be_slice).collect();
                            let cd = encode("verify(uint256[],bytes32,bytes)", |a| {
                                a.uints(&claims).uint(U256::from_be_bytes(ctx_c.tail[0])).bytes(&matrix_c)
                            });
                            let prefix = 3 + 1 + claims.len() + 1;
                            start_hash(&Ctx {
                                call: 1,
                                calldata: CallData::new(cd, prefix, None),
                                tail: [keccak256(out).0, [0u8; 32], [0u8; 32]],
                            })
                        } else {
                            terminal(REJECTED)
                        }
                    }
                    _ => terminal(REJECTED),
                }
            };
            let calldata = step_calldata(&pre.pre(&ctx_c), &cap.pre, &ctx_c, &witness);
            sink.lock().unwrap().push((calldata, pre.hash(&ctx_c), after, op));
        });
        let capture = Capture::new((0..400).collect(), None, on).stopping_after(400);
        let (_, sinkback) = machine.call_traced_gas(target, data, Some(Box::new(capture)), 1 << 40);
        drop(sinkback.expect("sink").into_any());
        let cases = std::mem::take(&mut *cases.lock().unwrap());
        for (calldata, before, after, op) in cases {
            let out = machine.call(onestep, calldata);
            let good = out.success && out.output.len() == 64 && B256::from_slice(&out.output[..32]) == before && B256::from_slice(&out.output[32..]) == after;
            steps_checked += 1;
            ops_seen.insert(op);
            if after == terminal(REJECTED) {
                kinds[1] += 1;
            } else {
                kinds[0] += 1;
            }
            if !good {
                failures += 1;
                if verbose && failures <= 20 {
                    println!(
                        "MISMATCH program {p} op 0x{op:02x}: success {} {}",
                        out.success,
                        if out.success { format!("after ok {}", B256::from_slice(&out.output[32..]) == after) } else { hex::encode(&out.output) }
                    );
                }
            }
        }
        kinds[2] += 1;
    }
    return FuzzReport {
        programs: kinds[2],
        steps: steps_checked,
        continuing: kinds[0],
        rejecting: kinds[1],
        opcodes: ops_seen.len(),
        mismatches: failures,
    };
}
