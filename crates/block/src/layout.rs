// SPDX-License-Identifier: LGPL-3.0-or-later

//! Geometry of the response block: where the head, the published words and every Keccak-f
//! sub-block sit.

use crate::keccak::{STATE0_BASE, STATE24_BASE, SUB_BITS, SUB_LOG};

/// Byte rate of Keccak-256.
pub const RATE_BYTES: usize = 136;

/// Bits of a Keccak-256 digest, and of a PRG tape block.
pub const DIGEST_BITS: usize = 256;

/// Bits of a PRG seed.
pub const SEED_BITS: usize = 256;

/// Bytes of a view-commitment preimage before the absorbed stream: tag, length and seed.
pub const VIEW_PREFIX_BYTES: usize = 21 + 8 + 32;

/// Head column of challenge bit `h_p`, set exactly when the challenge is `p`.
pub const fn h_col(p: usize) -> u32 {
    return (128 + p) as u32;
}

/// The word-level shape of a lifted statement, per slot: what the replay draws, absorbs and
/// outputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementShape {
    /// Input words per word width (8, 32, 64), in input order within each width.
    pub inputs: [usize; 3],
    /// AND-message words per word width.
    pub and_msgs: [usize; 3],
    /// Output words per word width.
    pub outputs: [usize; 3],
}

/// The word widths the block handles, in the order their words are laid out.
pub const WIDTHS: [usize; 3] = [8, 32, 64];

impl StatementShape {
    fn bits(counts: &[usize; 3]) -> usize {
        return counts.iter().zip(WIDTHS).map(|(n, w)| n * w).sum();
    }

    /// Bits of the party-2 input share.
    pub fn input_bits(&self) -> usize {
        return Self::bits(&self.inputs);
    }

    /// Bits of the AND messages, which is also the bits of gate tape drawn per slot.
    pub fn and_msg_bits(&self) -> usize {
        return Self::bits(&self.and_msgs);
    }

    /// Bits of one output share.
    pub fn output_bits(&self) -> usize {
        return Self::bits(&self.outputs);
    }

    /// Bits absorbed into one view commitment after its prefix.
    pub fn stream_bits(&self) -> usize {
        return self.input_bits() + self.and_msg_bits();
    }
}

/// The kind of a Keccak-f sub-block within one slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubKind {
    /// The PRG key derivation.
    Key,
    /// A PRG tape block, by counter.
    Prg(usize),
    /// A view-commitment sponge permutation, by block.
    Sponge(usize),
}

/// Geometry of a response block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Geometry {
    shape: StatementShape,
    k_log: usize,
    head_subs: usize,
    in_blocks: usize,
    prg_blocks: usize,
    sponge_blocks: usize,
}

impl Geometry {
    /// Lays out a block for `shape` with `k_log` block bits, or `None` if its Keccak-f sub-blocks
    /// leave fewer than `head_bits` bits of head.
    pub fn new(shape: StatementShape, k_log: usize, head_bits: usize) -> Option<Self> {
        let input_bits = shape.input_bits();
        assert!(
            input_bits % DIGEST_BITS == 0,
            "the input share must fill whole PRG blocks, got {input_bits} bits"
        );
        let in_blocks = input_bits / DIGEST_BITS;
        let prg_blocks = in_blocks + shape.and_msg_bits().div_ceil(DIGEST_BITS);
        let preimage_bytes = VIEW_PREFIX_BYTES + shape.stream_bits() / 8;
        let sponge_blocks = preimage_bytes / RATE_BYTES + 1;
        let subs = 2 * (1 + prg_blocks + sponge_blocks);
        let total_subs = 1usize << k_log.checked_sub(SUB_LOG)?;
        let head_subs = total_subs.checked_sub(subs)?;
        if head_subs * SUB_BITS < head_bits {
            return None;
        }
        return Some(Self {
            shape,
            k_log,
            head_subs,
            in_blocks,
            prg_blocks,
            sponge_blocks,
        });
    }

    /// The statement shape.
    pub fn shape(&self) -> &StatementShape {
        return &self.shape;
    }

    /// log2 of the block width.
    pub fn k_log(&self) -> usize {
        return self.k_log;
    }

    /// Bits available to the head.
    pub fn head_bits(&self) -> usize {
        return self.head_subs * SUB_BITS;
    }

    /// Number of head sub-block slots.
    pub fn head_subs(&self) -> usize {
        return self.head_subs;
    }

    /// PRG tape blocks per slot drawn for the input share.
    pub fn in_blocks(&self) -> usize {
        return self.in_blocks;
    }

    /// PRG tape blocks per slot.
    pub fn prg_blocks(&self) -> usize {
        return self.prg_blocks;
    }

    /// Sponge permutations per slot.
    pub fn sponge_blocks(&self) -> usize {
        return self.sponge_blocks;
    }

    /// Keccak-f sub-blocks per slot.
    pub fn subs_per_slot(&self) -> usize {
        return 1 + self.prg_blocks + self.sponge_blocks;
    }

    /// Total Keccak-f sub-blocks.
    pub fn keccak_subs(&self) -> usize {
        return 2 * self.subs_per_slot();
    }

    /// Sub-block index of a Keccak-f sub-block.
    pub fn sub_index(&self, slot: usize, kind: SubKind) -> usize {
        assert!(slot < 2);
        let local = match kind {
            SubKind::Key => 0,
            SubKind::Prg(i) => {
                assert!(i < self.prg_blocks);
                1 + i
            }
            SubKind::Sponge(i) => {
                assert!(i < self.sponge_blocks);
                1 + self.prg_blocks + i
            }
        };
        return self.head_subs + slot * self.subs_per_slot() + local;
    }

    /// First column of a Keccak-f sub-block.
    pub fn sub_base(&self, slot: usize, kind: SubKind) -> u32 {
        return (self.sub_index(slot, kind) << SUB_LOG) as u32;
    }

    /// Column of input-state bit `p`, in byte order, of a sub-block.
    pub fn state0_col(&self, slot: usize, kind: SubKind, p: usize) -> u32 {
        return self.sub_base(slot, kind) + (STATE0_BASE + p) as u32;
    }

    /// Column of output-state bit `p`, in byte order, of a sub-block.
    pub fn state24_col(&self, slot: usize, kind: SubKind, p: usize) -> u32 {
        return self.sub_base(slot, kind) + (STATE24_BASE + p) as u32;
    }

    /// Column of gate-tape bit `k` of a slot, for a slot that does not draw its input share.
    ///
    /// A slot that does draw it reads the same bit from the block one input share further on,
    /// which the tape counters absorb.
    pub fn gate_tape_col(&self, slot: usize, k: usize) -> u32 {
        return self.state24_col(slot, SubKind::Prg(self.in_blocks + k / DIGEST_BITS), k % DIGEST_BITS);
    }

    /// Column of input-tape bit `k` of a slot.
    pub fn input_tape_col(&self, slot: usize, k: usize) -> u32 {
        return self.state24_col(slot, SubKind::Prg(k / DIGEST_BITS), k % DIGEST_BITS);
    }

    /// Words of one published output share.
    pub fn out_words(&self) -> usize {
        return self.shape.output_bits().div_ceil(128);
    }

    /// Published word-columns: the challenge word, both view digests, and both output shares.
    pub fn io_word_cols(&self) -> Vec<usize> {
        return (1..6 + 2 * self.out_words()).collect();
    }

    /// Head column of bit `p` of a slot's view digest.
    pub fn digest_col(&self, slot: usize, p: usize) -> u32 {
        return (256 + slot * 256 + p) as u32;
    }

    /// Head column of bit `p` of a slot's output share.
    pub fn out_col(&self, slot: usize, p: usize) -> u32 {
        return (768 + slot * 128 * self.out_words() + p) as u32;
    }

    /// First head column after the published words.
    pub fn free_base(&self) -> u32 {
        return (128 * (6 + 2 * self.out_words())) as u32;
    }

    /// Head column of bit `p` of a slot's seed.
    pub fn seed_col(&self, slot: usize, p: usize) -> u32 {
        return self.free_base() + (slot * SEED_BITS + p) as u32;
    }

    /// Head column of bit `p` of the party-2 input share.
    pub fn x_col(&self, p: usize) -> u32 {
        return self.free_base() + (2 * SEED_BITS + p) as u32;
    }

    /// Head column of bit `p` of the AND messages.
    pub fn m_col(&self, p: usize) -> u32 {
        return self.x_col(self.shape.input_bits() + p);
    }

    /// First head column available to the replay.
    pub fn replay_base(&self) -> u32 {
        return self.m_col(self.shape.and_msg_bits());
    }

    /// Whether a sub-block index holds a Keccak-f permutation.
    pub fn is_keccak_sub(&self, sub: usize) -> bool {
        return sub >= self.head_subs && sub < self.head_subs + self.keccak_subs();
    }
}
