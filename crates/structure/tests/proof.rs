// SPDX-License-Identifier: LGPL-3.0-or-later

//! A structure proof over a toy block, two table types and a small wiring: acceptance of honest
//! claims and refusal of every wrong one.

use std::time::Instant;

use flock_prover::{
    challenger::FsChallenger,
    field::F128,
    lincheck::build_eq_table,
    matrix_fold::{MatrixClaim, Weight, bilinear},
    r1cs::SparseBinaryMatrix,
};
use pofseed_flock_lift_block::{committed::operations, program::Program, toy::Toy};
use pofseed_flock_lift_structure::{
    key::{Held, Parts, StructKey, Table},
    proof::{Claims, StructError, StructProof, prove, verify},
};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        return self.0;
    }

    fn f128(&mut self) -> F128 {
        return F128::new(self.next(), self.next());
    }

    fn vec(&mut self, n: usize) -> Vec<F128> {
        return (0..n).map(|_| self.f128()).collect();
    }
}

fn matrix(rng: &mut Rng, k: usize, per_row: usize) -> SparseBinaryMatrix {
    let n = 1usize << k;
    let rows = (0..n)
        .map(|_| {
            let mut row: Vec<usize> = (0..per_row).map(|_| rng.next() as usize % n).collect();
            row.sort_unstable();
            row.dedup();
            row
        })
        .collect();
    return SparseBinaryMatrix::new(n, n, rows);
}

fn table_claims(rng: &mut Rng, m: &SparseBinaryMatrix, k: usize, count: usize) -> Vec<MatrixClaim> {
    return (0..count)
        .map(|_| {
            let row = Weight::low_eq(rng.vec(64), rng.vec(k - 6));
            let col = Weight::low_eq(rng.vec(64), rng.vec(k - 6));
            let value = bilinear(&row, &col, m);
            MatrixClaim { row, col, value }
        })
        .collect();
}

fn embedded(x: usize) -> F128 {
    return F128::new(x as u64, 0);
}

struct Fixture {
    key: StructKey,
    claims: Claims,
}

fn fixture() -> Fixture {
    let mut rng = Rng(0x0bad_cafe_dead_beef);
    let program = Program::new(&Toy);
    let g = program.geometry();
    let (nu, mu) = (4usize, 7usize);
    let live: Vec<usize> = (0..1 << (mu - nu)).map(|_| rng.next() as usize % 17).collect();
    let cells: Vec<usize> = live.iter().enumerate().flat_map(|(s, &c)| (0..c).map(move |r| s << nu | r)).collect();
    let mut sigma: Vec<usize> = (0..1 << mu).collect();
    for i in (1..cells.len()).rev() {
        let j = rng.next() as usize % (i + 1);
        let (a, b) = (cells[i], cells[j]);
        sigma.swap(a, b);
    }
    let tables = vec![
        Table { k_log: 8, a: matrix(&mut rng, 8, 30), b: matrix(&mut rng, 8, 20) },
        Table { k_log: 7, a: matrix(&mut rng, 7, 2), b: matrix(&mut rng, 7, 1) },
    ];
    let k = g.k_log();
    let block = [true, false].map(|a_side| {
        let (row, col) = (rng.vec(k), rng.vec(k));
        let value = program.bilinear_eq(a_side, &row, &col);
        (row, col, value)
    });
    let table_claims = vec![
        [table_claims(&mut rng, &tables[0].a, 8, 2), table_claims(&mut rng, &tables[0].b, 8, 2)],
        [table_claims(&mut rng, &tables[1].a, 7, 1), table_claims(&mut rng, &tables[1].b, 7, 1)],
    ];
    let rho = rng.vec(mu);
    let eq = build_eq_table(&rho);
    let mut planes = [F128::ZERO; 3];
    for &x in &cells {
        planes[0] += eq[x];
        planes[1] += eq[x] * embedded(x);
        planes[2] += eq[x] * embedded(sigma[x]);
    }
    let t = Instant::now();
    let key = StructKey::new(
        Parts {
            k_log: k,
            head_subs: g.head_subs(),
            keccak_subs: g.keccak_subs(),
            operations: operations(&program),
            tables,
            nu,
            mu,
            live,
            sigma,
        },
        1,
    );
    println!("key over 2^{} bytes in {:.2} s", key.layout.n, t.elapsed().as_secs_f64());
    assert!(matches!(key.layout.tables[0].1, Held::Dense(_)) && matches!(key.layout.tables[1].1, Held::Small(_)));
    return Fixture {
        key,
        claims: Claims {
            block,
            tables: table_claims,
            cells: (rho, planes),
        },
    };
}

const DOMAIN: &[u8] = b"structure-test";

fn check(f: &Fixture, claims: &Claims, proof: &StructProof) -> Result<(), StructError> {
    return verify(&f.key.verifying(), claims, proof, &mut FsChallenger::new(DOMAIN));
}

#[test]
fn a_structure_proof_accepts_honest_claims_and_refuses_wrong_ones() {
    let f = fixture();
    let t = Instant::now();
    let proof = prove(&f.key, &f.claims, &mut FsChallenger::new(DOMAIN));
    println!(
        "proved in {:.2} s, {} B of which the opening {} B",
        t.elapsed().as_secs_f64(),
        bincode::serialize(&proof).unwrap().len(),
        bincode::serialize(&proof.opening).unwrap().len()
    );
    let t = Instant::now();
    assert_eq!(check(&f, &f.claims, &proof), Ok(()));
    println!("verified in {:.3} s", t.elapsed().as_secs_f64());

    // A wrong claim proved by an honest prover is refused where it is checked.
    let wrong = |edit: &dyn Fn(&mut Claims)| -> Result<(), StructError> {
        let mut claims = f.claims.clone();
        edit(&mut claims);
        let proof = prove(&f.key, &claims, &mut FsChallenger::new(DOMAIN));
        check(&f, &claims, &proof)
    };
    assert_eq!(wrong(&|c| c.block[0].2 += F128::ONE), Err(StructError::Operations), "a wrong block value on A");
    assert_eq!(wrong(&|c| c.block[1].2 += F128::ONE), Err(StructError::Operations), "a wrong block value on B");
    assert_eq!(wrong(&|c| c.cells.1[0] += F128::ONE), Err(StructError::Cells), "a wrong live value");
    assert_eq!(wrong(&|c| c.cells.1[1] += F128::ONE), Err(StructError::Cells), "a wrong identity value");
    assert_eq!(wrong(&|c| c.cells.1[2] += F128::ONE), Err(StructError::Cells), "a wrong wiring value");
    assert!(wrong(&|c| c.tables[0][1][1].value += F128::ONE).is_err(), "a wrong value on a dense table");
    assert!(wrong(&|c| c.tables[1][0][0].value += F128::ONE).is_err(), "a wrong value on a small table");

    // An honest proof does not serve other claims.
    let mut other = f.claims.clone();
    other.block[0].0[3] += F128::ONE;
    assert!(check(&f, &other, &proof).is_err(), "another block point");
    let mut other = f.claims.clone();
    other.cells.0[1] += F128::ONE;
    assert!(check(&f, &other, &proof).is_err(), "another wiring point");
    let mut other = f.claims.clone();
    other.tables[0][0][0].row.low[5] += F128::ONE;
    assert!(check(&f, &other, &proof).is_err(), "another table weight");

    // Every part of the proof refuses tampering.
    let tamper = |edit: &dyn Fn(&mut StructProof)| -> Result<(), StructError> {
        let mut p = proof.clone();
        edit(&mut p);
        check(&f, &f.claims, &p)
    };
    assert!(tamper(&|p| p.kernel_values[0] += F128::ONE).is_err(), "a kernel share");
    assert!(tamper(&|p| p.mask += F128::ONE).is_err(), "the mask");
    assert!(tamper(&|p| p.ops[20] += F128::ONE).is_err(), "a descriptor bit");
    assert!(tamper(&|p| p.kernel += F128::ONE).is_err(), "the tensor's value");
    assert!(tamper(&|p| p.cells[2] += F128::ONE).is_err(), "a cell bit");
    assert!(tamper(&|p| p.small[1] += F128::ONE).is_err(), "a small entry bit");
    assert!(tamper(&|p| p.ops_rounds.messages[1][4] += F128::ONE).is_err(), "an operations round");
    assert!(tamper(&|p| p.kernel_rounds.messages[9][0] += F128::ONE).is_err(), "a tensor round");
    assert!(tamper(&|p| p.folds[0][0].bridge[1] += F128::ONE).is_err(), "a fold");
    assert_eq!(tamper(&|p| p.roots[2][0][0] += F128::ONE), Err(StructError::Roots), "a root");
    assert_eq!(tamper(&|p| p.values[1][3] += F128::ONE), Err(StructError::Bits), "an opened value");
    assert!(tamper(&|p| p.opening.sumcheck[0][0] += flock_prover::field::F256::ONE).is_err(), "the opening");

    // Another commitment does not accept the proof.
    let mut vk = f.key.verifying();
    vk.commitment.cap[0][0] ^= 1;
    assert_eq!(verify(&vk, &f.claims, &proof, &mut FsChallenger::new(DOMAIN)), Err(StructError::Opening));
}
