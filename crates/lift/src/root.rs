// SPDX-License-Identifier: LGPL-3.0-or-later

//! A wrap verified without evaluating a fixed table: every evaluation its outer proof leaves to
//! the verifier becomes a claim, and a structure proof discharges the claims against a commitment
//! made once per statement and lift shape.

use std::sync::Arc;

use flock_prover::{
    field::F128,
    matrix_fold::{MatrixClaim, bilinear},
    pcs::OuterPcs,
    tower::{WrapKey, WrapProof},
    union::UnionInstance,
};
use pofseed_flock_lift_block::{committed::operations, program::Program};
use pofseed_flock_lift_structure::{
    key::{Parts, StructKey, StructVk, Table},
    proof::{Claims, StructProof},
};

use crate::{
    transcript::KeccakChallenger,
    wrap::{WrapError, matrix_claims, outer_transcript},
};

/// What discharging a wrap's claims needs: the commitment to the fixed tables, and the table each
/// Boolean table type of the wrap circuit shares.
pub struct RootKey {
    /// The commitment to the fixed tables.
    pub structure: StructKey,
    /// Per Boolean table type, in registry order, its table.
    pub table_of: Vec<usize>,
    /// The digest of the wrap circuit the tables are of.
    pub circuit: [u8; 32],
}

/// What verifying a discharge needs.
#[derive(Clone)]
pub struct RootVk {
    /// The commitment to the fixed tables.
    pub structure: StructVk,
    /// Per Boolean table type, in registry order, its table.
    pub table_of: Vec<usize>,
}

impl RootKey {
    /// The fixed tables of `program`'s block and of the wrap circuit of `key`, with the table each
    /// Boolean type of the circuit uses.
    pub fn parts(program: &Program, key: &WrapKey) -> (Parts, Vec<usize>) {
        let shape = &key.key.shape;
        let mut tables: Vec<Table> = Vec::new();
        let mut table_of = Vec::new();
        for ty in shape.registry.boolean_types() {
            let found = tables.iter().position(|t| Arc::ptr_eq(&t.a.rows, &ty.a_0.rows) && Arc::ptr_eq(&t.b.rows, &ty.b_0.rows));
            table_of.push(found.unwrap_or_else(|| {
                tables.push(Table {
                    k_log: ty.k_log,
                    a: ty.a_0.clone(),
                    b: ty.b_0.clone(),
                });
                tables.len() - 1
            }));
        }
        let cells = shape.circuit.cells();
        let g = program.geometry();
        let parts = Parts {
            k_log: g.k_log(),
            head_subs: g.head_subs(),
            keccak_subs: g.keccak_subs(),
            operations: operations(program),
            tables,
            nu: cells.nu(),
            mu: cells.mu(),
            live: shape.circuit.live_mask().counts,
            sigma: shape.circuit.sigma().to_vec(),
        };
        return (parts, table_of);
    }

    /// Commits to the fixed tables of `program`'s block and of the wrap circuit of `key`, at rate
    /// `2^-log_inv_rate`.
    pub fn new(program: &Program, key: &WrapKey, log_inv_rate: usize) -> Self {
        let (parts, table_of) = Self::parts(program, key);
        return Self {
            structure: StructKey::new(parts, log_inv_rate),
            table_of,
            circuit: key.key.digest(),
        };
    }

    /// What verifying needs.
    pub fn verifying(&self) -> RootVk {
        return RootVk {
            structure: self.structure.verifying(),
            table_of: self.table_of.clone(),
        };
    }
}

/// Verifies a wrap's outer proof with every evaluation of a fixed table left as a claim, checks the
/// element tables' evaluations against the tables, and returns the claims with the transcript.
pub fn outer_claims(
    key: &WrapKey,
    table_of: &[usize],
    proof: &WrapProof,
    outer: Option<&dyn OuterPcs>,
) -> Result<(Claims, KeccakChallenger), WrapError> {
    let mut ch = outer_transcript(&proof.public);
    let (work, sigma) = key.key.verify_deferred(proof, outer, &mut ch).map_err(|e| WrapError::Outer(format!("{e:?}")))?;
    let shape = &key.key.shape;
    let registry = &shape.registry;
    let union = UnionInstance::new(registry, shape.counts.clone());
    let n_tables = table_of.iter().max().map_or(0, |m| m + 1);
    let mut tables: Vec<[Vec<MatrixClaim>; 2]> = vec![[Vec::new(), Vec::new()]; n_tables];
    if let Some(boolean) = &work.boolean {
        boolean.check_reported(registry).map_err(|e| WrapError::Outer(format!("{e:?}")))?;
        for ((a, b), &t) in boolean.claims(registry).into_iter().zip(table_of) {
            tables[t][0].push(a);
            tables[t][1].push(b);
        }
    }
    if let Some(element) = &work.element {
        element.check_reported(&union).map_err(|e| WrapError::Outer(format!("{e:?}")))?;
        for ((a, b), ty) in element.claims(&union).into_iter().zip(registry.element_types()) {
            let ty = ty.element_type().expect("an element type");
            if bilinear(&a.row, &a.col, ty.a_0()) != a.value || bilinear(&b.row, &b.col, ty.b_0()) != b.value {
                return Err(WrapError::Element);
            }
        }
    }
    let claims = Claims {
        block: matrix_claims(key, proof).map(|(row, col, value): (Vec<F128>, Vec<F128>, F128)| (row, col, value)),
        tables,
        cells: (sigma.rho.clone(), [sigma.live_value, sigma.masked_id_value, sigma.value]),
    };
    return Ok((claims, ch));
}

/// Proves the claims the outer proof of a wrap leaves about the fixed tables.
pub fn prove_structure(
    root: &RootKey,
    key: &WrapKey,
    proof: &WrapProof,
    outer: Option<&dyn OuterPcs>,
) -> Result<StructProof, WrapError> {
    let (claims, mut ch) = outer_claims(key, &root.table_of, proof, outer)?;
    return Ok(pofseed_flock_lift_structure::proof::prove(&root.structure, &claims, &mut ch));
}

/// Verifies a wrap's outer proof and the structure proof of what it leaves about the fixed tables.
pub fn verify_root(
    vk: &RootVk,
    key: &WrapKey,
    proof: &WrapProof,
    structure: &StructProof,
    outer: Option<&dyn OuterPcs>,
) -> Result<(), WrapError> {
    let (claims, mut ch) = outer_claims(key, &vk.table_of, proof, outer)?;
    return pofseed_flock_lift_structure::proof::verify(&vk.structure, &claims, structure, &mut ch).map_err(WrapError::Structure);
}
