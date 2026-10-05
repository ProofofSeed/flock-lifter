// Added to the vendored copy of Flock; see VENDORED.md at the vendored root.
//! A polynomial commitment the merged opening can use in place of Ligerito.

use std::any::Any;

use crate::{challenger::Challenger, field::F128, merkle::Hash};

/// A commitment scheme over the dense stack's GF(2^128) words that opens their multilinear
/// extension at one point.
pub trait OuterPcs: Send + Sync {
    /// Commits to `words`, returning the cap the transcript binds and the prover's retained state.
    fn commit(&self, words: &[F128]) -> (Vec<Hash>, Box<dyn Any + Send + Sync>);
    /// Proves the words' multilinear extension at `point`, the transcript having bound the cap.
    fn open(
        &self,
        state: Box<dyn Any + Send + Sync>,
        point: &[F128],
        challenger: &mut dyn Challenger,
    ) -> Vec<u8>;
    /// Checks a proof that the committed words' multilinear extension is `value` at `point`.
    fn verify(
        &self,
        cap: &[Hash],
        point: &[F128],
        value: F128,
        proof: &[u8],
        challenger: &mut dyn Challenger,
    ) -> bool;
}
