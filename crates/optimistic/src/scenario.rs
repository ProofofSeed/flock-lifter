// SPDX-License-Identifier: LGPL-3.0-or-later

//! The verification of one lift as the direct route performs it: a call to the lift contract,
//! which returns the chunks' matrix claims, then a call to the matrix contract on those claims,
//! the lift's statement digest and the matrix proof.

use std::{fs, sync::Arc};

use pofseed_flock_lift::lift::{LiftKey, LiftedProof, MAX_CHUNK, Statement, prove, verify};
use pofseed_flock_lift_block::program::Program;
use pofseed_flock_lift_evm::{
    calldata::{encode_lift, encode_matrix},
    evm::{artifact, encode, immutable_offsets},
};
use pofseed_flock_lift_host::{HARDENED_OFFSET, bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{H, HardenedChildCircuit};
use revm::primitives::{Address, B256, U256, keccak256};
use zkboo_circuit_hash::hash_circuit;

use crate::machine::Machine;

/// The binding every scenario's ZKBoo proof is bound to.
pub const BINDING: &[u8] = b"flock-lifter evm-bench binding";

/// The entropy every scenario's ZKBoo proof is drawn from.
pub const ENTROPY: &[u8] = b"flock-lifter evm-bench entropy";

/// Number of calls in one verification.
pub const CALLS: usize = 2;

/// The lift version tag of the statement digest.
const LIFT_VERSION: &[u8] = b"pofseed-flock-lift-v1";

/// The statement a lift contract pins.
#[derive(Clone, Debug)]
pub struct Pinned {
    /// The circuit fingerprint.
    pub fingerprint: [u8; 32],
    /// The chain code.
    pub chain_code: [u8; 32],
    /// The child index.
    pub index: u32,
}

impl Pinned {
    /// The statement digest of a lift of `n` responses in chunks of `chunk` against `output`
    /// under `binding`, as the lift contract computes it.
    pub fn digest(&self, output: &[u8], binding: &[u8], n: u32, chunk: u32) -> B256 {
        let mut buf = Vec::new();
        let mut framed = |tag: &[u8], body: &[u8]| {
            buf.extend_from_slice(tag);
            buf.extend_from_slice(&(body.len() as u64).to_le_bytes());
            buf.extend_from_slice(body);
        };
        framed(LIFT_VERSION, &self.fingerprint);
        framed(b"chain-code", &self.chain_code);
        framed(b"index", &self.index.to_le_bytes());
        framed(b"expected-output", output);
        framed(b"binding", binding);
        framed(b"responses", &(n as u64).to_le_bytes());
        framed(b"chunk", &chunk.to_le_bytes());
        return keccak256(&buf);
    }
}

/// The chunk size and response count a lift's encoding starts with.
pub fn header(proof: &[u8]) -> (u32, u32) {
    return (
        u32::from_be_bytes(proof[..4].try_into().expect("chunk")),
        u32::from_be_bytes(proof[4..8].try_into().expect("responses")),
    );
}

/// The verification of one lift, ready to run.
pub struct Scenario {
    /// The lift program's address.
    pub lift: Address,
    /// The matrix program's address.
    pub matrix: Address,
    /// The statement the lift program pins.
    pub pinned: Pinned,
    /// The cap hash, profile, first Keccak sub-block and sub-block count the matrix program pins.
    pub matrix_params: [U256; 4],
    /// The code offsets of the lift program's three pins, then of the matrix program's four.
    pub pin_at: [usize; 7],
    /// The expected output, as serialised bytes.
    pub output: Vec<u8>,
    /// The output's word counts.
    pub counts: U256,
    /// The lift's calldata encoding.
    pub proof: Vec<u8>,
    /// The matrix proof's calldata encoding.
    pub matrix_proof: Vec<u8>,
}

/// Every call's calldata and outputs.
#[derive(Clone, Debug)]
pub struct Run {
    /// Whether each call returned.
    pub success: Vec<bool>,
    /// Output of each call.
    pub outputs: Vec<Vec<u8>>,
    /// Gas of each call.
    pub gas: Vec<u64>,
}

/// The code offsets of the first three immutables of `lift` and the first four of `matrix`.
fn pin_offsets(lift: (&str, &str), matrix: (&str, &str)) -> [usize; 7] {
    let l = immutable_offsets(lift.0, lift.1);
    let m = immutable_offsets(matrix.0, matrix.1);
    return [l[0], l[1], l[2], m[0], m[1], m[2], m[3]];
}

/// The words of an ABI-encoded `uint256[]` starting at `at` in `out`.
pub fn words_at(out: &[u8], at: usize) -> Vec<U256> {
    let n = U256::from_be_slice(&out[at..at + 32]).to::<usize>();
    return (0..n).map(|i| U256::from_be_slice(&out[at + 32 + 32 * i..at + 64 + 32 * i])).collect();
}

impl Scenario {
    /// Builds the scenario for an `n`-response lift, read from `cache` or proved and written
    /// there, and installs its two programs in `machine`: both exceed EIP-170's limit, so neither
    /// is deployed, and the one-step contract holds their runtime code as data.
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
        let key = LiftKey::new(program.clone());
        let lifted: LiftedProof = match fs::read(cache).ok() {
            Some(bytes) => bincode::deserialize(&bytes).expect("cached lift"),
            None => {
                assert!(n <= 8, "proving a lift of more than 8 responses is not done here");
                let lifted = prove(&key, &statement, &proof, MAX_CHUNK).expect("lift");
                fs::write(cache, bincode::serialize(&lifted).expect("serialise")).expect("write cache");
                lifted
            }
        };
        let vk = key.verifying();
        verify(&vk, &statement, &lifted).expect("the native verifier accepts");
        let fingerprint = hash_circuit::<_, H>(&statement.circuit());
        let mut code = artifact("FlockLift.sol", "FlockLift");
        code.extend_from_slice(&fingerprint);
        code.extend_from_slice(&chain_code);
        code.extend_from_slice(&U256::from(HARDENED_OFFSET).to_be_bytes::<32>());
        code.extend_from_slice(&U256::from(n).to_be_bytes::<32>());
        let y = &statement.expected_output;
        let counts = U256::from(y.as_vec::<u8>().len() | (y.as_vec::<u32>().len() << 16) | (y.as_vec::<u64>().len() << 32));
        code.extend_from_slice(&counts.to_be_bytes::<32>());
        code.extend_from_slice(&U256::ZERO.to_be_bytes::<32>());
        let lift = machine.install(Machine::runtime_code(code));
        let g = program.geometry();
        let matrix_params = [
            U256::from_be_bytes(keccak256(vk.matrix.commitment.cap.concat()).0),
            U256::ZERO,
            U256::from(g.head_subs()),
            U256::from(g.keccak_subs()),
        ];
        let mut code = artifact("FlockMatrix.sol", "FlockMatrix");
        for v in matrix_params {
            code.extend_from_slice(&v.to_be_bytes::<32>());
        }
        let matrix = machine.install(Machine::runtime_code(code));
        let pinned = Pinned {
            fingerprint: fingerprint.as_slice().try_into().expect("fingerprint"),
            chain_code: chain_code.as_slice().try_into().expect("chain code"),
            index: HARDENED_OFFSET,
        };
        let proof = encode_lift(&lifted);
        let (chunk, responses) = header(&proof);
        assert_eq!(
            pinned.digest(&y.as_bytes(), BINDING, responses, chunk).0,
            statement.digest(n, lifted.chunk),
            "the digest port agrees with the lifter's"
        );
        return Self {
            lift,
            matrix,
            pinned,
            matrix_params,
            pin_at: pin_offsets(("FlockLift.sol", "FlockLift"), ("FlockMatrix.sol", "FlockMatrix")),
            output: y.as_bytes(),
            counts,
            matrix_proof: encode_matrix(lifted.matrix.as_ref().expect("a matrix proof"), &vk.matrix),
            proof,
        };
    }

    /// A scenario of the same shape over stand-in contracts whose verification is a few
    /// thousand steps, deployed into `machine`: the stand-in lift rejects a proof starting with
    /// `0xff`, and the stand-in matrix contract one whose first byte is not its claims' first
    /// byte or whose digest is not the statement's.
    pub fn mock(machine: &mut Machine) -> Self {
        let pinned = Pinned {
            fingerprint: [0x5a; 32],
            chain_code: [0xc3; 32],
            index: 0x8000_0007,
        };
        let mut code = artifact("Mock.sol", "MockLift");
        code.extend_from_slice(&pinned.fingerprint);
        code.extend_from_slice(&pinned.chain_code);
        code.extend_from_slice(&U256::from(pinned.index).to_be_bytes::<32>());
        let (lift, _) = machine.deploy(code);
        let matrix_params = [
            U256::from_be_bytes(keccak256(b"stand-in entry commitment").0),
            U256::ZERO,
            U256::from(7),
            U256::from(11),
        ];
        let mut code = artifact("Mock.sol", "MockMatrix");
        for v in matrix_params {
            code.extend_from_slice(&v.to_be_bytes::<32>());
        }
        let (matrix, _) = machine.deploy(code);
        let mut proof = vec![0, 0, 0, 128, 0, 0, 0, 3];
        proof.extend((0..300u32).map(|i| (i.wrapping_mul(40_503) >> 3) as u8 | 1));
        let output = b"stand-in expected output".to_vec();
        let mut scenario = Self {
            lift,
            matrix,
            pinned,
            matrix_params,
            pin_at: pin_offsets(("Mock.sol", "MockLift"), ("Mock.sol", "MockMatrix")),
            output,
            counts: U256::from(24),
            proof,
            matrix_proof: Vec::new(),
        };
        let mut machine_out = machine.call(lift, scenario.lift_calldata(&scenario.proof));
        assert!(machine_out.success, "the stand-in lift accepts");
        let claims = words_at(&std::mem::take(&mut machine_out.output), 32);
        let mut matrix_proof = vec![claims[0].to_be_bytes::<32>()[0]];
        matrix_proof.extend((0..700u32).map(|i| (i.wrapping_mul(2_654_435_761) >> 13) as u8));
        scenario.matrix_proof = matrix_proof;
        return scenario;
    }

    /// The contract call `i` goes to.
    pub fn target(&self, i: usize) -> Address {
        return if i == 0 { self.lift } else { self.matrix };
    }

    /// The statement digest of a lift whose encoding is `proof`.
    pub fn digest(&self, proof: &[u8]) -> B256 {
        let (chunk, n) = header(proof);
        return self.pinned.digest(&self.output, BINDING, n, chunk);
    }

    /// The lift contract's calldata for proof bytes `proof`.
    pub fn lift_calldata(&self, proof: &[u8]) -> Vec<u8> {
        return encode("verify(bytes,uint256,bytes,bytes)", |a| {
            a.bytes(&self.output).uint(self.counts).bytes(BINDING).bytes(proof)
        });
    }

    /// Calldata of call `i` for the lift `proof` and matrix proof `matrix`, given the outputs of
    /// the calls before it.
    pub fn calldata(&self, i: usize, outputs: &[Vec<u8>], proof: &[u8], matrix: &[u8]) -> Vec<u8> {
        return match i {
            0 => self.lift_calldata(proof),
            1 => {
                let claims = words_at(&outputs[0], 32);
                let digest = self.digest(proof);
                encode("verify(uint256[],bytes32,bytes)", |a| {
                    a.uints(&claims).uint(U256::from_be_bytes(digest.0)).bytes(matrix)
                })
            }
            _ => panic!("no call {i}"),
        };
    }

    /// Runs every call in turn on the scenario's own proofs, stopping at the first that fails.
    pub fn run(&self, machine: &mut Machine) -> Run {
        let mut run = Run {
            success: Vec::new(),
            outputs: Vec::new(),
            gas: Vec::new(),
        };
        for i in 0..CALLS {
            let data = self.calldata(i, &run.outputs, &self.proof, &self.matrix_proof);
            let out = machine.call(self.target(i), data);
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
