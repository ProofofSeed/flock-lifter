// SPDX-License-Identifier: LGPL-3.0-or-later

//! The lifted statement and the relying-party gate, as in the SP1 lifter.

use crate::S;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};
use zkboo::word::Words;

/// Version tag of the [`LiftJournal`] layout.
pub const LIFT_JOURNAL_VERSION: u32 = 3;

/// The ZKBoo proof format this statement is defined over.
pub const REQUIRED_PROOF_FORMAT_ID: [u8; 32] = [
    0x4b, 0xe5, 0xd4, 0xe6, 0x4c, 0x11, 0xba, 0x4d, 0x40, 0xe7, 0x89, 0x77, 0xf6, 0x8d, 0x45, 0xad,
    0x8b, 0xf0, 0x1f, 0xe3, 0x1a, 0xa2, 0x75, 0x07, 0xe8, 0xdd, 0xca, 0x20, 0x22, 0x3a, 0x73, 0x70,
];

/// The lifted statement a verified lift attests.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LiftJournal {
    /// Journal layout version.
    pub version: u32,
    /// Whether the ZKBoo proof verified.
    pub valid: bool,
    /// Structural fingerprint of the verified circuit.
    pub fingerprint: S,
    /// Parent chain code.
    pub chain_code: Vec<u8>,
    /// Child index.
    pub index: u32,
    /// The circuit output the proof was verified against.
    pub expected_output: Words,
    /// The challenge binding the proof was verified under.
    pub binding: Vec<u8>,
    /// Number of responses in the verified proof.
    pub num_responses: u32,
    /// The ZKBoo proof format the verifier was built against.
    pub proof_format_id: [u8; 32],
}

/// What a relying party requires of a [`LiftJournal`].
pub struct JournalExpectation {
    /// Required circuit fingerprint.
    pub fingerprint: S,
    /// Required parent chain code.
    pub chain_code: Vec<u8>,
    /// Required child index.
    pub index: u32,
    /// Required circuit output.
    pub expected_output: Words,
    /// Required challenge binding.
    pub binding: Vec<u8>,
    /// Minimum acceptable number of responses.
    pub min_responses: u32,
    /// Required ZKBoo proof format identity.
    pub proof_format_id: [u8; 32],
}

/// Why a [`LiftJournal`] was refused by [`check_journal`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JournalCheckError {
    /// The journal layout version is not [`LIFT_JOURNAL_VERSION`].
    VersionMismatch,
    /// The verdict is not `true`.
    NotValid,
    /// The circuit fingerprint differs from the required one.
    FingerprintMismatch,
    /// Chain code, index or expected output differ from the required statement.
    StatementMismatch,
    /// The binding differs from the required one.
    BindingMismatch,
    /// Fewer responses than the required minimum.
    TooFewResponses,
    /// The ZKBoo proof format differs from the required one.
    ProofFormatMismatch,
    /// The expected output carries no u8 words, so it has no assertion word.
    AssertionWordMissing,
    /// The expected output's trailing assertion word is not 1.
    AssertionWordNotSet,
}

/// Checks a [`LiftJournal`] against a [`JournalExpectation`], including the assertion word, which
/// is required of the journal itself whatever the expectation says.
pub fn check_journal(
    journal: &LiftJournal,
    expectation: &JournalExpectation,
) -> Result<(), JournalCheckError> {
    if journal.version != LIFT_JOURNAL_VERSION {
        return Err(JournalCheckError::VersionMismatch);
    }
    if !journal.valid {
        return Err(JournalCheckError::NotValid);
    }
    if journal.fingerprint != expectation.fingerprint {
        return Err(JournalCheckError::FingerprintMismatch);
    }
    if journal.chain_code != expectation.chain_code
        || journal.index != expectation.index
        || journal.expected_output != expectation.expected_output
    {
        return Err(JournalCheckError::StatementMismatch);
    }
    if journal.binding != expectation.binding {
        return Err(JournalCheckError::BindingMismatch);
    }
    if journal.num_responses < expectation.min_responses {
        return Err(JournalCheckError::TooFewResponses);
    }
    if journal.proof_format_id != expectation.proof_format_id {
        return Err(JournalCheckError::ProofFormatMismatch);
    }
    match journal.expected_output.as_vec::<u8>().last() {
        None => return Err(JournalCheckError::AssertionWordMissing),
        Some(&w) if w != 1 => return Err(JournalCheckError::AssertionWordNotSet),
        Some(_) => {}
    }
    return Ok(());
}

#[cfg(test)]
mod assertion_word_tests {
    use super::*;
    use alloc::vec;

    fn pair(assertion: u8) -> (LiftJournal, JournalExpectation) {
        let mut output = Words::new();
        output.as_vec_mut::<u8>().extend_from_slice(&[0xde, 0xad, assertion]);
        let journal = LiftJournal {
            version: LIFT_JOURNAL_VERSION,
            valid: true,
            fingerprint: [7u8; 32],
            chain_code: vec![1u8; 32],
            index: 0,
            expected_output: output.clone(),
            binding: vec![],
            num_responses: 219,
            proof_format_id: REQUIRED_PROOF_FORMAT_ID,
        };
        let expectation = JournalExpectation {
            fingerprint: [7u8; 32],
            chain_code: vec![1u8; 32],
            index: 0,
            expected_output: output,
            binding: vec![],
            min_responses: 219,
            proof_format_id: REQUIRED_PROOF_FORMAT_ID,
        };
        return (journal, expectation);
    }

    #[test]
    fn a_set_assertion_word_is_accepted() {
        let (journal, expectation) = pair(1);
        assert!(check_journal(&journal, &expectation).is_ok());
    }

    #[test]
    fn a_clear_assertion_word_is_refused_even_when_the_expectation_agrees() {
        let (journal, expectation) = pair(0);
        assert_eq!(
            check_journal(&journal, &expectation),
            Err(JournalCheckError::AssertionWordNotSet)
        );
    }
}
