// SPDX-License-Identifier: LGPL-3.0-or-later

//! Checkpoints of a verification: the transcript's state at the end of each stage, which the
//! contract emits too.

use std::cell::RefCell;

use pofseed_flock_lift::transcript::KeccakChallenger;

thread_local! {
    static MARKS: RefCell<Vec<(u32, [u8; 32])>> = const { RefCell::new(Vec::new()) };
}

/// Records the state of `tr` under `id`: its chaining value with the pending bytes folded in.
pub fn mark(id: u32, tr: &KeccakChallenger) {
    let state = tr.clone().digest();
    MARKS.with(|m| m.borrow_mut().push((id, state)));
}

/// Takes the checkpoints recorded on this thread.
pub fn take() -> Vec<(u32, [u8; 32])> {
    return MARKS.with(|m| std::mem::take(&mut *m.borrow_mut()));
}
