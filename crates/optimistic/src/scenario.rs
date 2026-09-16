// SPDX-License-Identifier: LGPL-3.0-or-later

//! The verification of one lift as a fixed sequence of calls to the two verifier contracts: the
//! lift contract, then the matrix discharge's Keccak part, its stream in one segment, and its
//! final check. Each later call's calldata is built from earlier calls' outputs.

use std::{fs, sync::Arc};

use pofseed_flock_lift::lift::{LiftedProof, MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::encode_lift,
    discharge::Stream,
    evm::{artifact, encode},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit};
use revm::primitives::{Address, U256};
use zkboo_circuit_hash::hash_circuit;

use crate::machine::Machine;

/// The binding every scenario's ZKBoo proof is bound to.
pub const BINDING: &[u8] = b"flock-lifter evm-bench binding";

/// The entropy every scenario's ZKBoo proof is drawn from.
pub const ENTROPY: &[u8] = b"flock-lifter evm-bench entropy";

/// Number of calls in one verification.
pub const CALLS: usize = 4;

/// The verification of one lift, ready to run.
pub struct Scenario {
    /// Responses in the lift.
    pub n: usize,
    /// The block.
    pub program: Arc<Program>,
    /// The discharge stream, in one segment.
    pub stream: Stream,
    /// The lift contract's deployed address.
    pub lift: Address,
    /// The discharge contract's deployed address.
    pub discharge: Address,
    /// The lift contract's constructor arguments.
    pub lift_args: Vec<u8>,
    /// The discharge contract's constructor arguments.
    pub discharge_args: Vec<u8>,
    /// The expected output, as serialised bytes.
    pub output: Vec<u8>,
    /// The output's word counts.
    pub counts: U256,
    /// The lift's calldata encoding.
    pub proof: Vec<u8>,
}

/// The four calls' calldata and outputs.
#[derive(Clone, Debug)]
pub struct Run {
    /// Calldata of each call.
    pub calldata: Vec<Vec<u8>>,
    /// Whether each call returned.
    pub success: Vec<bool>,
    /// Output of each call.
    pub outputs: Vec<Vec<u8>>,
    /// Gas of each call.
    pub gas: Vec<u64>,
}

/// The words of an ABI-encoded `uint256[]` starting at `at` in `out`.
pub fn words_at(out: &[u8], at: usize) -> Vec<U256> {
    let n = U256::from_be_slice(&out[at..at + 32]).to::<usize>();
    return (0..n).map(|i| U256::from_be_slice(&out[at + 32 + 32 * i..at + 64 + 32 * i])).collect();
}

impl Scenario {
    /// Builds the scenario for an `n`-response lift, read from `cache` or proved and written
    /// there, and deploys its contracts into `machine`.
    pub fn new(machine: &mut Machine, n: usize, cache: &str) -> Self {
        let (_, chain_code) = bip32_vector_1();
        let (_, output, proof) = vector_1_proof(n, ENTROPY, BINDING);
        let statement = Statement {
            chain_code: chain_code.clone(),
            index: HARDENED_OFFSET,
            expected_output: output,
            binding: BINDING.to_vec(),
        };
        let program = Arc::new(Program::new(&HardenedChildCircuit::public_only(chain_code.clone(), HARDENED_OFFSET)));
        let lifted: LiftedProof = match fs::read(cache).ok() {
            Some(bytes) => bincode::deserialize(&bytes).expect("cached lift"),
            None => {
                assert!(n <= 8, "proving a lift of more than 8 responses is not done here");
                let lifted = prove(&program, &statement, &proof, MAX_CHUNK).expect("lift");
                fs::write(cache, bincode::serialize(&lifted).expect("serialise")).expect("write cache");
                lifted
            }
        };
        verify(&program, &statement, &lifted).expect("the native verifier accepts");
        let mut lift_args = hash_circuit::<_, H>(&statement.circuit()).to_vec();
        lift_args.extend_from_slice(&chain_code);
        lift_args.extend_from_slice(&U256::from(HARDENED_OFFSET).to_be_bytes::<32>());
        lift_args.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
        lift_args.extend_from_slice(&U256::ZERO.to_be_bytes::<32>());
        let mut code = artifact("FlockLift.sol", "FlockLift");
        code.extend_from_slice(&lift_args);
        let (lift, _) = machine.deploy(code);
        let stream = Stream::new(&program, usize::MAX);
        let g = program.geometry();
        let mut discharge_args = Vec::new();
        for v in [g.k_log(), g.head_subs(), g.subs_per_slot(), g.prg_blocks(), g.in_blocks(), stream.head_words] {
            discharge_args.extend_from_slice(&U256::from(v).to_be_bytes::<32>());
        }
        discharge_args.extend_from_slice(&stream.digest());
        let mut code = artifact("Discharge.sol", "FlockDischarge");
        code.extend_from_slice(&discharge_args);
        let (discharge, _) = machine.deploy(code);
        let y = &statement.expected_output;
        let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
        return Self {
            n,
            program,
            stream,
            lift,
            discharge,
            lift_args,
            discharge_args,
            output: y.as_bytes(),
            counts,
            proof: encode_lift(&lifted),
        };
    }

    /// The contract call `i` goes to.
    pub fn target(&self, i: usize) -> Address {
        return if i == 0 { self.lift } else { self.discharge };
    }

    /// The lift contract's calldata for proof bytes `proof`.
    pub fn lift_calldata(&self, proof: &[u8]) -> Vec<u8> {
        return encode("verify(bytes,uint256,bytes,bytes)", |a| {
            a.bytes(&self.output).uint(self.counts).bytes(BINDING).bytes(proof)
        });
    }

    /// Calldata of call `i` given the outputs of the calls before it.
    pub fn calldata(&self, i: usize, outputs: &[Vec<u8>], proof: &[u8]) -> Vec<u8> {
        return match i {
            0 => self.lift_calldata(proof),
            1 => encode("keccakPart(uint256[])", |a| a.uints(&words_at(&outputs[0], 32))),
            2 => {
                let claims = words_at(&outputs[0], 32);
                let state = vec![U256::ZERO; 2 * claims.len() / 112];
                encode("rows(uint256[],uint256[],bytes32,bytes)", |a| {
                    a.uints(&claims).uints(&state).uint(U256::ZERO).bytes(&self.stream.segments[0])
                })
            }
            3 => {
                let claims = words_at(&outputs[0], 32);
                let part = words_at(&outputs[1], 32);
                let offset = U256::from_be_slice(&outputs[2][..32]).to::<usize>();
                let state = words_at(&outputs[2], offset);
                let chain = U256::from_be_slice(&outputs[2][32..64]);
                encode("finish(uint256[],uint256[],uint256[],bytes32)", |a| {
                    a.uints(&claims).uints(&part).uints(&state).uint(chain)
                })
            }
            _ => panic!("no call {i}"),
        };
    }

    /// Runs every call in turn, stopping at the first that fails.
    pub fn run(&self, machine: &mut Machine, proof: &[u8]) -> Run {
        let mut run = Run {
            calldata: Vec::new(),
            success: Vec::new(),
            outputs: Vec::new(),
            gas: Vec::new(),
        };
        for i in 0..CALLS {
            let data = self.calldata(i, &run.outputs, proof);
            let out = machine.call(self.target(i), data.clone());
            run.calldata.push(data);
            run.success.push(out.success);
            run.outputs.push(out.output);
            run.gas.push(out.gas);
            if !out.success {
                break;
            }
        }
        return run;
    }
}
