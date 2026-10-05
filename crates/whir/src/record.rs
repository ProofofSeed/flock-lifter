// SPDX-License-Identifier: LGPL-3.0-or-later
//! A WHIR opening as the data Flock's in-circuit WHIR verifier consumes.

use crate::domain::Domain;
use crate::params::Config;
use crate::whir::{Commitment, Openings, Proof};
use flock_prover::field::F128;
use flock_prover::tower::{WhirFunction, WhirRecord};

fn rows_and_paths(o: &Openings, lanes: usize) -> (Vec<Vec<F128>>, Vec<Vec<[u8; 32]>>) {
    match o {
        Openings::Base(rows, paths) => {
            (rows.chunks(lanes).map(<[F128]>::to_vec).collect(), paths.clone())
        }
        Openings::Ext(rows, paths) => (
            rows.chunks(lanes).map(|r| r.iter().flat_map(|e| [e.c0, e.c1]).collect()).collect(),
            paths.clone(),
        ),
    }
}

/// The record of an opening of `commitment` under `config` with `points` evaluation claims.
pub fn whir_record(
    config: &Config,
    commitment: &Commitment,
    proof: &Proof,
    points: usize,
) -> WhirRecord {
    let schedule = config.schedule().expect("a secure configuration");
    let rounds = &schedule.rounds;
    let functions = rounds
        .iter()
        .enumerate()
        .map(|(i, r)| {
            let openings = if i + 1 < rounds.len() {
                &proof.rounds[i].openings
            } else {
                &proof.final_openings
            };
            let (rows, paths) = rows_and_paths(openings, 1 << r.fold);
            let cap = if i == 0 { commitment.cap.clone() } else { proof.rounds[i - 1].cap.clone() };
            WhirFunction {
                fold: r.fold,
                log_domain: r.log_domain,
                queries: r.queries,
                next_vars: rounds.get(i + 1).map_or(schedule.final_vars, |n| n.vars),
                vars: r.vars,
                ood: r.ood,
                table: Domain::new(r.log_domain).table().to_vec(),
                ext: i > 0,
                rows,
                paths,
                cap,
            }
        })
        .collect();
    WhirRecord { functions, num_vars: config.num_vars, final_vars: schedule.final_vars, points }
}
