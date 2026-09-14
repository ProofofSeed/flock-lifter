// SPDX-License-Identifier: LGPL-3.0-or-later

//! Tampered and malformed responses for refusal tests.

use pofseed_flock_lift_statement::S;
use zkboo::{prover::proof::Response, word::Words};

/// A copy of `response` with one AND-message bit flipped.
pub fn tamper_and_msg(response: &Response<S, S>) -> Response<S, S> {
    let mut msg = response.and_msg_next_party().clone();
    if !msg.as_vec::<u64>().is_empty() {
        msg.as_vec_mut::<u64>()[0] ^= 1;
    } else if !msg.as_vec::<u32>().is_empty() {
        msg.as_vec_mut::<u32>()[0] ^= 1;
    } else {
        msg.as_vec_mut::<u8>()[0] ^= 1;
    }
    return rebuild_response(response, msg);
}

/// A copy of `response` with one extra word appended to its AND messages.
pub fn oversize_and_msg(response: &Response<S, S>) -> Response<S, S> {
    let mut msg = response.and_msg_next_party().clone();
    msg.as_vec_mut::<u64>().push(0);
    return rebuild_response(response, msg);
}

fn rebuild_response(response: &Response<S, S>, msg: Words) -> Response<S, S> {
    let seeds = response.seeds();
    let digest = *response.commitment_digest_unopened();
    return match response.challenge().index() {
        0 => Response::new_0(*seeds[0], *seeds[1], digest, msg),
        1 => Response::new_1(digest, *seeds[0], *seeds[1], msg, response.input_share_2().unwrap().clone()),
        _ => Response::new_2(*seeds[1], digest, *seeds[0], msg, response.input_share_2().unwrap().clone()),
    };
}
