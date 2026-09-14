// SPDX-License-Identifier: LGPL-3.0-or-later

//! A Flock proof over a batch of response blocks, publishing each block's words.

use std::sync::Arc;

use flock_prover::{
    bits::transpose_8_u64s_to_64_bytes,
    challenger::FsChallenger,
    circuit::builder::{BuiltCircuit, CircuitBuilder, GateType, SlotWitness},
    field::F128,
    pcs::{
        Commitment, PcsParams,
        ligerito::{LigeritoProfile, embedded_initial_k_or_default},
    },
    proof::R1csProofCircuitMerged,
    prover::{UnionSlotProverInput, prove_fast_ligerito_union_circuit},
    r1cs::SparseBinaryMatrix,
    schedule::{IoWord, TableClass, TableType},
    union::{SlotWitnessDest, UnionInstance},
    verifier::{FlockVerifyError, verify_ligerito_union_circuit},
};
use pofseed_flock_lift_block::program::{Program, WitnessError};
use pofseed_flock_lift_statement::S;
use rayon::prelude::*;
use zkboo::prover::proof::Response;

/// Smallest committed size Ligerito has a configuration for.
const MIN_DENSE_M: usize = 22;

/// The Ligerito profile every chunk is proved under.
pub const PROFILE: LigeritoProfile = LigeritoProfile::Fast;

/// A Flock proof over a batch of response blocks.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ChunkProof {
    /// The Flock proof.
    pub proof: R1csProofCircuitMerged,
    /// The witness commitment.
    pub commitment: Commitment,
}

/// Why a chunk proof was refused.
#[derive(Debug)]
pub enum ChunkError {
    /// A block's published words have the wrong length.
    PublicLength,
    /// The proof commits under parameters other than the chunk's.
    Parameters,
    /// Flock's verifier refused the proof.
    Flock(FlockVerifyError),
}

struct ResponseGate {
    program: Arc<Program>,
}

impl GateType for ResponseGate {
    type Row = ();
    type Hint = Vec<F128>;

    fn table(&self) -> TableType {
        let stub = || SparseBinaryMatrix::new(0, 0, Vec::new());
        return TableType {
            k_log: self.program.geometry().k_log(),
            useful_bits: self.program.block_bits(),
            a_0: stub(),
            b_0: stub(),
            c_0: stub(),
            const_pin: Some(0),
            class: TableClass::Boolean,
            io_schema: self
                .program
                .geometry()
                .io_word_cols()
                .into_iter()
                .map(IoWord::output)
                .collect(),
        };
    }

    fn eval(&self, _inputs: &[F128], hint: &Vec<F128>, outputs: &mut Vec<F128>) {
        outputs.extend_from_slice(hint);
    }

    fn witness(&self, _rows: &[()], _nu: usize) -> SlotWitness {
        return SlotWitness::DeferredToRows;
    }
}

fn row_log(count: usize) -> usize {
    return (count.next_power_of_two().trailing_zeros() as usize).max(3);
}

fn circuit_for(program: &Arc<Program>, publics: &[Vec<F128>]) -> BuiltCircuit {
    let mut builder = CircuitBuilder::new(row_log(publics.len()));
    let slot = builder.slot(ResponseGate {
        program: program.clone(),
    });
    for words in publics {
        for w in builder.gate_with_hint(slot, &[], words.clone()) {
            builder.publish(w);
        }
    }
    return builder.finish().expect("a batch of response blocks is a valid circuit");
}

fn union_for(built: &BuiltCircuit) -> UnionInstance<'_> {
    let mut union = UnionInstance::new(&built.shape.registry, built.shape.counts.clone());
    if union.dense_m() < MIN_DENSE_M {
        union.set_dense_floor(MIN_DENSE_M);
    }
    return union;
}

fn pcs_params(union: &UnionInstance<'_>) -> PcsParams {
    let m = union.dense_m();
    let log_batch_size = embedded_initial_k_or_default(m, PROFILE);
    return PcsParams {
        m,
        log_inv_rate: PROFILE.log_inv_rate(),
        log_batch_size,
        profile: PROFILE,
        num_lanes: union.commit_lanes(log_batch_size),
        merkle_hash: Default::default(),
    };
}

#[derive(Clone, Copy)]
struct SendPtr<T>(*mut T);

unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

fn fill(program: &Program, responses: &[Response<S, S>], nu: usize, dst: SlotWitnessDest<'_>) -> Vec<u8> {
    let k = program.block_bits();
    let cols = k / 128;
    let rows = 1usize << nu;
    let timing = std::env::var_os("POFSEED_TIMING").is_some();
    let t = std::time::Instant::now();
    let SlotWitnessDest { z, a, b, .. } = dst;
    for buf in [&mut *z, &mut *a, &mut *b] {
        assert_eq!(buf.len(), cols << nu, "slot block length");
        buf.par_chunks_mut(1 << 20).for_each(|c| c.fill(F128::ZERO));
    }
    if timing {
        eprintln!("[pofseed] zero-fill {:.2} s", t.elapsed().as_secs_f64());
    }
    let t = std::time::Instant::now();
    let ptrs = [SendPtr(z.as_mut_ptr()), SendPtr(a.as_mut_ptr()), SendPtr(b.as_mut_ptr())];
    responses.par_iter().enumerate().for_each(|(j, response)| {
        let words = k / 64;
        let mut local = [vec![0u64; words], vec![0u64; words], vec![0u64; words]];
        let [lz, la, lb] = &mut local;
        program
            .write_witness(response, lz, la, lb)
            .expect("responses are checked before proving");
        for (ptr, buf) in ptrs.iter().zip(local.iter()) {
            for c in 0..cols {
                // SAFETY: row `j` owns index `(c << nu) + j` of every column, and rows are distinct.
                unsafe {
                    *ptr.0.add((c << nu) + j) = F128::new(buf[2 * c], buf[2 * c + 1]);
                }
            }
        }
    });
    if timing {
        eprintln!("[pofseed] witness generation and scatter {:.2} s", t.elapsed().as_secs_f64());
    }
    let t = std::time::Instant::now();
    let z: &[F128] = z;
    let mut stripe = vec![0u8; (rows / 8) * k];
    stripe.par_chunks_mut(k).enumerate().for_each(|(g, s)| {
        if 8 * g >= responses.len() {
            return;
        }
        for w in 0..k / 64 {
            let lanes: [u64; 8] = core::array::from_fn(|r| {
                let f = z[((w / 2) << nu) + 8 * g + r];
                if w % 2 == 0 { f.lo } else { f.hi }
            });
            transpose_8_u64s_to_64_bytes(&lanes, &mut s[64 * w..64 * w + 64]);
        }
    });
    if timing {
        eprintln!("[pofseed] lincheck stripe {:.2} s", t.elapsed().as_secs_f64());
    }
    return stripe;
}

/// Proves a batch of responses whose published words are `publics`, under the transcript
/// domain `domain`.
pub fn prove_chunk(
    program: &Arc<Program>,
    responses: &[Response<S, S>],
    publics: &[Vec<F128>],
    domain: &[u8],
) -> Result<ChunkProof, WitnessError> {
    assert_eq!(responses.len(), publics.len(), "one set of published words per response");
    for response in responses {
        program.check_response(response)?;
    }
    let built = circuit_for(program, publics);
    let union = union_for(&built);
    let params = pcs_params(&union);
    let nu = union.n_log();
    let input = UnionSlotProverInput::in_place(
        move |dst| fill(program, responses, nu, dst),
        program.as_ref(),
    );
    let mut challenger = FsChallenger::new(domain);
    let (proof, commitment, _) = prove_fast_ligerito_union_circuit(
        &union,
        &built.shape.circuit,
        &built.witness.public,
        &params,
        vec![input],
        Vec::new(),
        &mut challenger,
    );
    return Ok(ChunkProof { proof, commitment });
}

/// Verifies a chunk proof against the published words of its blocks.
pub fn verify_chunk(
    program: &Arc<Program>,
    publics: &[Vec<F128>],
    chunk: &ChunkProof,
    domain: &[u8],
) -> Result<(), ChunkError> {
    let n_io = program.geometry().io_word_cols().len();
    if publics.is_empty() || publics.iter().any(|p| p.len() != n_io) {
        return Err(ChunkError::PublicLength);
    }
    let built = circuit_for(program, publics);
    let union = union_for(&built);
    let params = pcs_params(&union);
    if chunk.commitment.params != params {
        return Err(ChunkError::Parameters);
    }
    let mut challenger = FsChallenger::new(domain);
    verify_ligerito_union_circuit(
        &union,
        &built.shape.circuit,
        &built.witness.public,
        &[program.as_ref()],
        &chunk.commitment,
        &chunk.proof,
        &params,
        &mut challenger,
    )
    .map_err(ChunkError::Flock)?;
    return Ok(());
}
