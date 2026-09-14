// SPDX-License-Identifier: LGPL-3.0-or-later

//! The published words of a response computed by ZKBoo's own view replay, independently of the
//! block.

use crate::program::Program;
use flock_prover::field::F128;
use pofseed_flock_lift_statement::{H, PV, S};
use zkboo::{
    circuit::Circuit,
    prover::proof::Response,
    verifier::replay::{OwnedFlexibleWordPairPool, ViewReplayError, ViewReplayerBackend},
    word::{Word, Words},
};

fn push_word_bits<W: Word>(words: &Words, bits: &mut Vec<bool>) {
    for &w in words.as_vec::<W>() {
        let one: W = W::ONE;
        for b in 0..W::WIDTH {
            bits.push((w >> b) & one == one);
        }
    }
}

/// The bits of a word store, widths 8, 32 and 64 in turn, each word least significant bit first.
pub fn words_bits(words: &Words) -> Vec<bool> {
    let mut bits = Vec::new();
    push_word_bits::<u8>(words, &mut bits);
    push_word_bits::<u32>(words, &mut bits);
    push_word_bits::<u64>(words, &mut bits);
    return bits;
}

/// Packs bits into `n` 128-bit words.
pub fn pack_bits(bits: &[bool], n: usize) -> Vec<F128> {
    let mut packed = vec![0u64; 2 * n];
    for (p, &bit) in bits.iter().enumerate() {
        packed[p / 64] |= (bit as u64) << (p % 64);
    }
    return packed.chunks(2).map(|w| F128::new(w[0], w[1])).collect();
}

/// The published words of `response` against `output`: the one-hot challenge word, the opened
/// slots' view digests and their output shares.
pub fn io_words<C: Circuit>(
    program: &Program,
    circuit: &C,
    output: &Words,
    response: &Response<S, S>,
) -> Result<Vec<F128>, ViewReplayError> {
    let frontend =
        ViewReplayerBackend::<H, PV, S, OwnedFlexibleWordPairPool<usize>>::new(response).into_view_replayer();
    circuit.exec(&frontend);
    let commitments = frontend.finalize_with_arg(output)?;
    let c = response.challenge().index();
    let mut words = vec![F128::new(1 << c, 0)];
    for s in 0..2 {
        let d = commitments[(c + s) % 3].digest();
        for k in 0..2 {
            let lo = u64::from_le_bytes(d[16 * k..16 * k + 8].try_into().unwrap());
            let hi = u64::from_le_bytes(d[16 * k + 8..16 * k + 16].try_into().unwrap());
            words.push(F128::new(lo, hi));
        }
    }
    for s in 0..2 {
        let bits = words_bits(commitments[(c + s) % 3].output_share());
        words.extend(pack_bits(&bits, program.geometry().out_words()));
    }
    return Ok(words);
}
