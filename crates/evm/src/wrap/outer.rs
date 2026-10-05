// SPDX-License-Identifier: LGPL-3.0-or-later

//! The verifier of a wrap's outer proof, as the contract computes it: Flock's deferred circuit
//! verifier with its transcript kept byte for byte, its divisions and table walks replaced by
//! closed forms, and every evaluation of a committed table left as a claim.

use flock_prover::{
    challenger::Challenger,
    field::F128,
    lincheck::build_eq_table,
    matrix_fold::{MatrixClaim, Weight},
    zerocheck::multilinear::lagrange_weights_naive,
};
use pofseed_flock_lift::{transcript::KeccakChallenger, wrap::WRAP_DOMAIN};
use pofseed_flock_lift_structure::proof::Claims;

use crate::{
    mirror::{Reader, Reject, Result, dot, pow_f128, read_n, zerocheck},
    wrap::vk::{Sparse, Vk},
};

/// Univariate-skip variables.
const K_SKIP: usize = 6;

/// A claim on the committed bits: a skip point, the word's upper bit coordinate, the row and the
/// column coordinates, and the value.
#[derive(Clone, Debug)]
pub struct BitClaim {
    /// The skip point.
    pub z: F128,
    /// The coordinate of a word's upper half.
    pub x0: F128,
    /// The row coordinates.
    pub row: Vec<F128>,
    /// The column coordinates.
    pub col: Vec<F128>,
    /// The claimed value.
    pub value: F128,
}

/// A claim on the committed words: the row and the column coordinates, and the value.
#[derive(Clone, Debug)]
pub struct WordClaim {
    /// The row coordinates.
    pub row: Vec<F128>,
    /// The column coordinates.
    pub col: Vec<F128>,
    /// The claimed value.
    pub value: F128,
}

/// What the interactive proofs before the opening leave.
pub struct Piops {
    /// The claims on the committed bits: on `A·z` and `B·z` jointly, then on `C·z`.
    pub bits: [BitClaim; 2],
    /// The element class's two claims on the committed words.
    pub words: [WordClaim; 2],
    /// The wiring point's row coordinates, which every gathered cell slot's claim shares.
    pub gather_row: Vec<F128>,
    /// The gathered cell slots' values.
    pub gather: Vec<F128>,
    /// The claims left on the committed tables.
    pub claims: Claims,
}

/// `Π_j eq(coords_j, bit_j(bits))`.
pub fn eq_prefix_weight(coords: &[F128], bits: usize) -> F128 {
    return coords.iter().enumerate().fold(F128::ONE, |acc, (j, &x)| acc * if bits >> j & 1 == 1 { x } else { F128::ONE + x });
}

/// `Σ_{i<n} eq(point, i)`.
pub fn eq_prefix_sum(point: &[F128], n: usize) -> F128 {
    if n >= 1 << point.len() {
        return F128::ONE;
    }
    let (mut acc, mut run) = (F128::ZERO, F128::ONE);
    for j in (0..point.len()).rev() {
        if n >> j & 1 == 1 {
            acc += run * (F128::ONE + point[j]);
            run *= point[j];
        } else {
            run *= F128::ONE + point[j];
        }
    }
    return acc;
}

/// The multilinear extension of `values`, zero-padded, at `point`, by folding its low variable
/// first.
pub fn fold_eval(values: &[F128], point: &[F128]) -> F128 {
    let mut v = values.to_vec();
    for &r in point {
        let half = v.len().div_ceil(2);
        for k in 0..half {
            let lo = v[2 * k];
            let hi = v.get(2 * k + 1).copied().unwrap_or(F128::ZERO);
            v[k] = lo + r * (lo + hi);
        }
        v.truncate(half);
    }
    assert_eq!(v.len(), 1, "the point spans the values");
    return v[0];
}

/// A quadratic round's claim at `r`, from the message `(g(1), g(∞))` and the previous claim.
pub fn quadratic(claim: F128, e1: F128, einf: F128, r: F128) -> F128 {
    let e0 = claim + e1;
    return einf * r * r + (e0 + e1 + einf) * r + e0;
}

/// Starts the outer transcript: the public segment, then Flock's statement binding.
fn bind(vk: &Vk, public: &[F128], cap: &[[u8; 32]], publics_digest: &[u8; 32]) -> KeccakChallenger {
    let mut tr = KeccakChallenger::new(WRAP_DOMAIN);
    tr.observe_label(b"pofseed-flock-lift-wrap-public");
    tr.observe_f128_slice(public);
    tr.observe_label(b"flock-mixed-v1");
    tr.observe_bytes(&vk.registry_digest);
    tr.observe_bytes(&vk.counts_le);
    tr.observe_bytes(cap.as_flattened());
    tr.observe_label(b"flock-circuit-stmt-v2");
    tr.observe_bytes(&vk.circuit_digest);
    tr.observe_bytes(publics_digest);
    return tr;
}

struct Lincheck {
    z: F128,
    rr: Vec<F128>,
    value: F128,
}

/// The Boolean class's lincheck over the union's columns, its reported table evaluations checked
/// against its last equation and left as claims.
fn lincheck(
    vk: &Vk,
    rd: &mut Reader,
    tr: &mut KeccakChallenger,
    skip: &[F128],
    x_inner_rest: &[F128],
    x_outer: &[F128],
    a: F128,
    b: F128,
    tables: &mut [[Vec<MatrixClaim>; 2]],
) -> Result<Lincheck> {
    let rounds = vk.m_bool - vk.nu - K_SKIP;
    tr.observe_label(b"flock-lincheck-v0");
    let alpha = pow_f128(tr, rd.nonce()?, 1)?;
    let mut target = alpha * a + b;
    let mut betas = Vec::with_capacity(vk.bools.len());
    for ty in &vk.bools {
        betas.push(match ty.pin {
            Some(_) => {
                let beta = pow_f128(tr, rd.nonce()?, 1)?;
                target += beta * eq_prefix_sum(x_outer, ty.count);
                Some(beta)
            }
            None => None,
        });
    }
    let mut rr = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let (e1, einf) = (rd.f128()?, rd.f128()?);
        tr.observe_f128(e1);
        tr.observe_f128(einf);
        let r = pow_f128(tr, rd.nonce()?, 2)?;
        target = quadratic(target, e1, einf, r);
        rr.push(r);
    }
    rr.reverse();
    let z_partial = read_n(rd, 1 << K_SKIP)?;
    tr.observe_f128_slice(&z_partial);
    let z = pow_f128(tr, rd.nonce()?, K_SKIP as u32)?;
    let value = dot(&lagrange_weights_naive(K_SKIP, z), &z_partial);
    let mut acc = F128::ZERO;
    for (ty, beta) in vk.bools.iter().zip(&betas) {
        let (va, vb) = (rd.f128()?, rd.f128()?);
        let inner = ty.k_log - K_SKIP;
        let w = eq_prefix_weight(&x_inner_rest[inner..], ty.prefix);
        let p = eq_prefix_weight(&rr[inner..], ty.prefix);
        acc += p * w * (alpha * va + vb);
        if let (Some(col), Some(beta)) = (ty.pin, beta) {
            acc += p * *beta * eq_prefix_weight(&rr[..inner], col >> K_SKIP) * z_partial[col & 63];
        }
        let row = Weight::low_eq(skip.to_vec(), x_inner_rest[..inner].to_vec());
        let col = Weight::low_eq(z_partial.clone(), rr[..inner].to_vec());
        for (side, value) in [va, vb].into_iter().enumerate() {
            tables[ty.table][side].push(MatrixClaim {
                row: row.clone(),
                col: col.clone(),
                value,
            });
        }
    }
    if acc != target {
        return Err(Reject("lincheck table evaluations"));
    }
    return Ok(Lincheck { z, rr, value });
}

struct Wiring {
    rho: Vec<F128>,
    cells: [F128; 3],
    gather: Vec<F128>,
}

/// The wiring argument: the grand-product layers, the input check against the supplied
/// evaluations of the live mask and of the masked identity, and the recombination of the gathered
/// values with the public words.
fn wiring(vk: &Vk, rd: &mut Reader, tr: &mut KeccakChallenger, public: &[F128]) -> Result<Wiring> {
    tr.observe_label(b"flock-product-gkr-batched-v0");
    let alpha = pow_f128(tr, rd.nonce()?, vk.gkr_bits)?;
    let beta = tr.sample_f128();
    let (top_l, top_r) = (rd.f128()?, rd.f128()?);
    tr.observe_f128(top_l);
    tr.observe_f128(top_r);
    if top_l != top_r {
        return Err(Reject("wiring products"));
    }
    let (mut claim_l, mut claim_r) = (top_l, top_r);
    let mut point: Vec<F128> = Vec::new();
    for k in 0..vk.mu {
        let lambda = pow_f128(tr, rd.nonce()?, 1)?;
        let mut running = claim_l + lambda * claim_r;
        let mut next = Vec::with_capacity(k + 1);
        for &r_eq in &point {
            let (g1, ginf) = (rd.f128()?, rd.f128()?);
            if r_eq == F128::ONE {
                return Err(Reject("degenerate round"));
            }
            let g0 = (running + r_eq * g1) * (F128::ONE + r_eq).inv();
            tr.observe_f128(g1);
            tr.observe_f128(ginf);
            let rho = pow_f128(tr, rd.nonce()?, 2)?;
            next.push(rho);
            running = g0 * (F128::ONE + rho) + g1 * rho + ginf * rho * (F128::ONE + rho);
        }
        let v = read_n(rd, 4)?;
        v.iter().for_each(|&x| tr.observe_f128(x));
        if running != v[0] * v[1] + lambda * (v[2] * v[3]) {
            return Err(Reject("wiring layer"));
        }
        let c = pow_f128(tr, rd.nonce()?, 1)?;
        claim_l = (F128::ONE + c) * v[0] + c * v[1];
        claim_r = (F128::ONE + c) * v[2] + c * v[3];
        next.push(c);
        point = next;
    }
    let v = read_n(rd, 5)?;
    let (f, g, sigma, live, masked) = (v[0], v[1], v[2], v[3], v[4]);
    let tail = (beta + F128::ONE) * live + F128::ONE;
    if claim_l != f + alpha * masked + tail || claim_r != g + alpha * sigma + tail {
        return Err(Reject("wiring inputs"));
    }
    [f, g, sigma].iter().for_each(|&x| tr.observe_f128(x));
    let gather = read_n(rd, vk.gate_cols.len())?;
    let (row, slot) = point.split_at(vk.nu);
    let eq_slot = build_eq_table(slot);
    let acc = dot(&eq_slot[..gather.len()], &gather) + eq_slot[vk.public_slot()] * fold_eval(public, row);
    if acc != f || f != g {
        return Err(Reject("wiring recombination"));
    }
    return Ok(Wiring {
        rho: point,
        cells: [live, masked, sigma],
        gather,
    });
}

/// `Σ_{r,c} row[r]·col[c]·m[r][c]`.
fn bilinear(m: &Sparse, row: &[F128], col: &[F128]) -> F128 {
    return m.iter().zip(row).fold(F128::ZERO, |acc, (entries, &r)| {
        if entries.is_empty() {
            return acc;
        }
        acc + r * entries.iter().fold(F128::ZERO, |a, &(c, v)| a + if v == F128::ONE { col[c] } else { v * col[c] })
    });
}

/// The element class's zerocheck and lincheck, its tables evaluated in place.
fn element(vk: &Vk, rd: &mut Reader, tr: &mut KeccakChallenger) -> Result<[WordClaim; 2]> {
    let (nu, vars) = (vk.nu, vk.m_elem - 7);
    tr.observe_label(b"flock-element-union-zc-v0");
    let bits = usize::BITS - vars.leading_zeros();
    let tau = crate::mirror::pow_vec(tr, rd.nonce()?, bits, vars)?;
    let mut running = F128::ZERO;
    let mut r = Vec::with_capacity(vars);
    for &t in &tau {
        let (g1, ginf) = (rd.f128()?, rd.f128()?);
        if t == F128::ONE {
            return Err(Reject("degenerate round"));
        }
        let g0 = (running + t * g1) * (F128::ONE + t).inv();
        tr.observe_f128(g1);
        tr.observe_f128(ginf);
        let rho = pow_f128(tr, rd.nonce()?, 2)?;
        r.push(rho);
        running = g0 * (F128::ONE + rho) + g1 * rho + ginf * rho * (F128::ONE + rho);
    }
    let (ea, eb, ec) = (rd.f128()?, rd.f128()?, rd.f128()?);
    if running != ea * eb + ec {
        return Err(Reject("element zerocheck"));
    }
    [ea, eb, ec].iter().for_each(|&x| tr.observe_f128(x));
    let rows: Vec<Vec<F128>> = vk.elems.iter().map(|t| build_eq_table(&r[nu..nu + t.kappa])).collect();
    let (mut va, mut vb) = (ea, eb);
    for (ty, eq) in vk.elems.iter().zip(&rows) {
        let w = eq_prefix_weight(&r[nu + ty.kappa..], ty.prefix);
        va += w * dot(&eq[..ty.a_const.len()], &ty.a_const);
        vb += w * dot(&eq[..ty.b_const.len()], &ty.b_const);
    }
    tr.observe_label(b"flock-element-union-lc-v0");
    let alpha = pow_f128(tr, rd.nonce()?, 1)?;
    let mut running = va + alpha * vb;
    let mut col = Vec::with_capacity(vars - nu);
    for _ in 0..vars - nu {
        let (e1, einf) = (rd.f128()?, rd.f128()?);
        tr.observe_f128(e1);
        tr.observe_f128(einf);
        let rho = pow_f128(tr, rd.nonce()?, 2)?;
        running = quadratic(running, e1, einf, rho);
        col.push(rho);
    }
    col.reverse();
    let z_eval = rd.f128()?;
    let mut acc = F128::ZERO;
    for (ty, row) in vk.elems.iter().zip(&rows) {
        let (ta, tb) = (rd.f128()?, rd.f128()?);
        let eq_col = build_eq_table(&col[..ty.kappa]);
        if bilinear(&ty.a, row, &eq_col) != ta || bilinear(&ty.b, row, &eq_col) != tb {
            return Err(Reject("element table evaluation"));
        }
        let w = eq_prefix_weight(&r[nu + ty.kappa..], ty.prefix) * eq_prefix_weight(&col[ty.kappa..], ty.prefix);
        acc += w * (ta + alpha * tb);
    }
    if acc * z_eval != running {
        return Err(Reject("element lincheck"));
    }
    let frozen = vk.elem_frozen.iter().map(|&b| if b { F128::ONE } else { F128::ZERO });
    let c_col: Vec<F128> = r[nu..].iter().copied().chain(frozen.clone()).collect();
    let lc_col: Vec<F128> = col.iter().copied().chain(frozen).collect();
    return Ok([
        WordClaim {
            row: r[..nu].to_vec(),
            col: c_col,
            value: ec,
        },
        WordClaim {
            row: r[..nu].to_vec(),
            col: lc_col,
            value: z_eval,
        },
    ]);
}

/// The public segment of a wrap: the fixed prefix, then the words read from calldata.
pub fn read_public(vk: &Vk, rd: &mut Reader) -> Result<Vec<F128>> {
    let mut public = vk.fixed.clone();
    public.extend(read_n(rd, vk.num_public - vk.fixed.len())?);
    return Ok(public);
}

/// The interactive proofs of a wrap's outer proof before its opening, on the transcript they
/// leave.
pub fn piops(vk: &Vk, rd: &mut Reader, public: &[F128]) -> Result<(Piops, KeccakChallenger, Vec<[u8; 32]>)> {
    let cap_len = pofseed_flock_lift_whir::merkle::cap_size(
        1 << vk.whir.schedule().map_err(|_| Reject("configuration"))?.rounds[0].log_domain,
        vk.whir.schedule().map_err(|_| Reject("configuration"))?.rounds[0].queries,
    );
    let cap: Vec<[u8; 32]> = (0..cap_len).map(|_| rd.hash()).collect::<Result<_>>()?;
    let digest = rd.hash()?;
    let mut tr = bind(vk, public, &cap, &digest);
    let mut child = tr.fork(b"flock-par-wiring-v1");
    let zc = zerocheck(vk.m_bool, rd, &mut tr)?;
    let nu = vk.nu;
    let skip = lagrange_weights_naive(K_SKIP, zc.z);
    let mut x_inner_rest = vec![zc.mlv[0]];
    x_inner_rest.extend_from_slice(&zc.mlv[1 + nu..]);
    let x_outer = &zc.mlv[1..1 + nu];
    let mut tables: Vec<[Vec<MatrixClaim>; 2]> = vec![[Vec::new(), Vec::new()]; vk.n_tables];
    let lc = lincheck(vk, rd, &mut tr, &skip, &x_inner_rest, x_outer, zc.a, zc.b, &mut tables)?;
    let zeros = vec![F128::ZERO; vk.m_total - vk.m_bool];
    let ab = BitClaim {
        z: lc.z,
        x0: lc.rr[0],
        row: x_outer.to_vec(),
        col: lc.rr[1..].iter().chain(&zeros).copied().collect(),
        value: lc.value,
    };
    let c = BitClaim {
        z: zc.z,
        x0: zc.r_rest[0],
        row: zc.r_rest[1..1 + nu].to_vec(),
        col: zc.r_rest[1 + nu..].iter().chain(&zeros).copied().collect(),
        value: zc.c,
    };
    let w = wiring(vk, rd, &mut child, public)?;
    tr.merge_child(child);
    let words = element(vk, rd, &mut tr)?;
    let block = [0, 1].map(|i| {
        let (at, k_col, k_row) = vk.acc[i];
        (public[at + k_col..at + k_col + k_row].to_vec(), public[at..at + k_col].to_vec(), public[at + k_col + k_row])
    });
    let claims = Claims {
        block,
        tables,
        cells: (w.rho.clone(), w.cells),
    };
    return Ok((
        Piops {
            bits: [ab, c],
            words,
            gather_row: w.rho[..nu].to_vec(),
            gather: w.gather,
            claims,
        },
        tr,
        cap,
    ));
}
