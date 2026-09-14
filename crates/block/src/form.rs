// SPDX-License-Identifier: LGPL-3.0-or-later

//! GF(2) linear forms over the columns of a block.

/// Column of the constant-one wire.
pub const CONST: u32 = 0;

/// A GF(2) linear form: the XOR of a sorted, duplicate-free set of columns.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Form {
    cols: Vec<u32>,
}

impl Form {
    /// The zero form.
    pub const fn zero() -> Self {
        return Self { cols: Vec::new() };
    }

    /// The form of a single column.
    pub fn col(col: u32) -> Self {
        return Self { cols: vec![col] };
    }

    /// The constant form of a bit.
    pub fn constant(bit: bool) -> Self {
        return if bit { Self::col(CONST) } else { Self::zero() };
    }

    /// The form of a set of columns, cancelling repeated columns in pairs.
    pub fn from_cols(mut cols: Vec<u32>) -> Self {
        cols.sort_unstable();
        let mut out: Vec<u32> = Vec::with_capacity(cols.len());
        for c in cols {
            if out.last() == Some(&c) {
                out.pop();
            } else {
                out.push(c);
            }
        }
        return Self { cols: out };
    }

    /// The columns of the form.
    pub fn cols(&self) -> &[u32] {
        return &self.cols;
    }

    /// Number of columns in the form.
    pub fn len(&self) -> usize {
        return self.cols.len();
    }

    /// Whether the form is zero.
    pub fn is_zero(&self) -> bool {
        return self.cols.is_empty();
    }

    /// Whether the form is the constant one.
    pub fn is_one(&self) -> bool {
        return self.cols.len() == 1 && self.cols[0] == CONST;
    }

    /// The single column of the form, if it has exactly one non-constant column.
    pub fn as_col(&self) -> Option<u32> {
        return match self.cols.as_slice() {
            [c] if *c != CONST => Some(*c),
            _ => None,
        };
    }

    /// The XOR of two forms.
    pub fn xor(&self, other: &Form) -> Form {
        let (a, b) = (&self.cols, &other.cols);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            if a[i] < b[j] {
                out.push(a[i]);
                i += 1;
            } else if b[j] < a[i] {
                out.push(b[j]);
                j += 1;
            } else {
                i += 1;
                j += 1;
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        return Form { cols: out };
    }

    /// XORs a form into this one.
    pub fn xor_assign(&mut self, other: &Form) {
        *self = self.xor(other);
    }

    /// Evaluates the form against a bit-packed assignment of the columns.
    pub fn eval(&self, z: &[u64]) -> bool {
        let mut acc = 0u64;
        for &c in &self.cols {
            acc ^= z[(c >> 6) as usize] >> (c & 63);
        }
        return acc & 1 == 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xor_cancels_and_stays_sorted() {
        let a = Form::from_cols(vec![5, 1, 9, 1, 3]);
        assert_eq!(a.cols(), &[3, 5, 9]);
        let b = Form::from_cols(vec![9, 2, 3]);
        assert_eq!(a.xor(&b).cols(), &[2, 5]);
        assert!(a.xor(&a).is_zero());
    }

    #[test]
    fn eval_reads_packed_bits() {
        let mut z = vec![0u64; 2];
        z[0] |= 1 << 3;
        z[1] |= 1 << 1;
        assert!(Form::from_cols(vec![3]).eval(&z));
        assert!(!Form::from_cols(vec![3, 65]).eval(&z));
        assert!(Form::from_cols(vec![3, 66]).eval(&z));
    }
}
