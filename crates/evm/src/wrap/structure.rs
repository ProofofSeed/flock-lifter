// SPDX-License-Identifier: LGPL-3.0-or-later

//! The proof of the committed tables' evaluations in calldata form, and its verification from
//! that form.

use flock_prover::{field::F128, matrix_fold::FoldProof};
use pofseed_flock_lift::transcript::KeccakChallenger;
use pofseed_flock_lift_structure::{
    key::{KERNEL_LOG, Layout, OP_BITS, StructVk},
    proof::{Claims, StructProof, reduce},
    subfield::DEGREE,
    sumcheck::Rounds,
};
use pofseed_flock_lift_whir::whir::{Openings, Proof};

use crate::{
    calldata::Writer,
    mirror::{Reader, Reject, Result, read_n},
    wrap::whir,
};

fn rounds(w: &mut Writer, r: &Rounds) {
    for (message, &nonce) in r.messages.iter().zip(&r.nonces) {
        message.iter().for_each(|&v| w.f128(v));
        w.nonce(nonce);
    }
}

fn read_rounds(rd: &mut Reader, vars: usize, degree: usize) -> Result<Rounds> {
    let mut r = Rounds {
        messages: Vec::with_capacity(vars),
        nonces: Vec::with_capacity(vars),
    };
    for _ in 0..vars {
        r.messages.push(read_n(rd, degree)?);
        r.nonces.push(rd.nonce()?);
    }
    return Ok(r);
}

/// The degrees of the sumchecks over the operations, the cells and the small entries.
fn degrees(layout: &Layout) -> (usize, usize, usize) {
    return (OP_BITS + 1, layout.mu + 2, 1 + layout.small_id + 2 * layout.small_index);
}

/// Encodes a structure proof under `vk` in the order its verifier reads it.
pub fn encode(vk: &StructVk, proof: &StructProof) -> Vec<u8> {
    let mut w = Writer::default();
    for (folds, &(k, _)) in proof.folds.iter().zip(&vk.layout.tables) {
        for f in folds {
            assert!(f.col_rounds.len() == k && f.row_rounds.len() == k && f.grinding_nonces.len() == 2 + 2 * k);
            w.nonce(f.grinding_nonces[0]);
            for (&(a, b), &n) in f.col_rounds.iter().zip(&f.grinding_nonces[1..1 + k]) {
                w.f128(a);
                w.f128(b);
                w.nonce(n);
            }
            f.bridge.iter().for_each(|&v| w.f128(v));
            w.nonce(f.grinding_nonces[1 + k]);
            for (&(a, b), &n) in f.row_rounds.iter().zip(&f.grinding_nonces[2 + k..]) {
                w.f128(a);
                w.f128(b);
                w.nonce(n);
            }
            w.f128(f.value);
        }
    }
    proof.kernel_values.iter().for_each(|&v| w.f128(v));
    w.nonce(proof.batching_nonce);
    rounds(&mut w, &proof.ops_bits_rounds);
    rounds(&mut w, &proof.ops_rounds);
    w.f128(proof.mask);
    proof.ops.iter().for_each(|&v| w.f128(v));
    rounds(&mut w, &proof.kernel_rounds);
    w.f128(proof.kernel);
    rounds(&mut w, &proof.cells_rounds);
    proof.cells.iter().for_each(|&v| w.f128(v));
    rounds(&mut w, &proof.small_rounds);
    proof.small.iter().for_each(|&v| w.f128(v));
    w.nonce(proof.bits_nonce);
    rounds(&mut w, &proof.batch_rounds);
    proof.roots.iter().flatten().for_each(|&v| w.f128(v));
    proof.values.iter().for_each(|&v| w.f128(v));
    w.raw(&whir::encode(&vk.config, &proof.opening));
    return w.bytes;
}

/// Verifies the proof `rd` holds of `claims` against the commitment of `vk`.
pub fn verify(vk: &StructVk, claims: &Claims, rd: &mut Reader, tr: &mut KeccakChallenger) -> Result<()> {
    let layout = &vk.layout;
    if claims.tables.len() != layout.tables.len() {
        return Err(Reject("claims shape"));
    }
    let mut folds = Vec::with_capacity(layout.tables.len());
    for (&(k, _), groups) in layout.tables.iter().zip(&claims.tables) {
        let mut pair = Vec::with_capacity(2);
        for group in groups {
            let mut nonces = vec![rd.nonce()?];
            let mut col_rounds = Vec::with_capacity(k);
            for _ in 0..k {
                col_rounds.push((rd.f128()?, rd.f128()?));
                nonces.push(rd.nonce()?);
            }
            let bridge = read_n(rd, group.len())?;
            nonces.push(rd.nonce()?);
            let mut row_rounds = Vec::with_capacity(k);
            for _ in 0..k {
                row_rounds.push((rd.f128()?, rd.f128()?));
                nonces.push(rd.nonce()?);
            }
            pair.push(FoldProof {
                col_rounds,
                bridge,
                row_rounds,
                value: rd.f128()?,
                grinding_nonces: nonces,
            });
        }
        let [a, b]: [FoldProof; 2] = pair.try_into().expect("two sides");
        folds.push([a, b]);
    }
    let (d_ops, d_cells, d_small) = degrees(layout);
    let kernel_values = [rd.f128()?, rd.f128()?];
    let batching_nonce = rd.nonce()?;
    let ops_bits_rounds = read_rounds(rd, 6, 3)?;
    let ops_rounds = read_rounds(rd, layout.ops.slots_log(), d_ops)?;
    let mask = rd.f128()?;
    let ops = read_n(rd, OP_BITS)?;
    let kernel_rounds = read_rounds(rd, KERNEL_LOG, 2)?;
    let kernel = rd.f128()?;
    let cells_rounds = read_rounds(rd, layout.cells.slots_log(), d_cells)?;
    let cells = read_n(rd, layout.cell_bits())?;
    let small_rounds = read_rounds(rd, layout.small.slots_log(), d_small)?;
    let small = read_n(rd, layout.small_bits())?;
    let bits_nonce = rd.nonce()?;
    let batch_rounds = read_rounds(rd, 3 + layout.n, 2)?;
    let roots = (0..DEGREE - 1).map(|_| read_n(rd, layout.n)).collect::<Result<Vec<Vec<F128>>>>()?;
    let values = read_n(rd, DEGREE)?;
    let proof = StructProof {
        folds,
        kernel_values,
        batching_nonce,
        ops_bits_rounds,
        ops_rounds,
        mask,
        ops,
        kernel_rounds,
        kernel,
        cells_rounds,
        cells,
        small_rounds,
        small,
        bits_nonce,
        batch_rounds,
        roots,
        values,
        opening: Proof {
            ood: Vec::new(),
            sumcheck: Vec::new(),
            rounds: Vec::new(),
            final_poly: Vec::new(),
            final_pow: 0,
            final_openings: Openings::Base(Vec::new(), Vec::new()),
        },
    };
    let (points, values) = reduce(layout, claims, &proof, tr).map_err(|_| Reject("table evaluations"))?;
    return whir::verify(&vk.config, &vk.commitment.cap, &points, &values, rd, tr);
}
