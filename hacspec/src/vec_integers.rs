#![allow(unused_variables)]
///!
///! Implement the `Numeric` trait for arrays.
///!

#[macro_export]
macro_rules! _implement_numeric_unsigned_public {
    ($name:ident, $elements:ty) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature="use_attributes", primitive(hacspec))]
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        impl $name {
            /// Check if the two sequences are compatible, i.e. have the same
            /// length.
            fn compatible(&self, other: &Self) -> bool {
                assert!(
                    self.len() == other.len(),
                    "Can't combine two sequences that don't have the same length."
                );
                if self.len() != other.len() {
                    return false;
                }
                return true;
            }
        }

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add(self, rhs: $name) -> $name {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].wrapping_add(rhs[i])
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub(self, rhs: $name) -> $name {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].wrapping_sub(rhs[i])
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul(self, rhs: $name) -> $name {
                self.compatible(&rhs);
                vec_mul(self, rhs, 0)
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: $name) -> $name {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].wrapping_div(rhs[i])
                }
                out
            }
        }

        /// Bit-wise not operation on the coefficients.
        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not(self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = !self[i]
                }
                out
            }
        }

        /// Bit-wise or operation on the coefficients.
        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitor(self, rhs: Self) -> Self::Output {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] | rhs[i]
                }
                out
            }
        }

        /// Bit-wise xor operation on the coefficients.
        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitxor(self, rhs: Self) -> Self::Output {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] ^ rhs[i]
                }
                out
            }
        }

        /// Bit-wise and operation on the coefficients.
        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitand(self, rhs: Self) -> Self::Output {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] & rhs[i]
                }
                out
            }
        }

        // TODO: is this a useful thing? Then implement it.
        /// **Unimplemented**
        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shr(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        // TODO: is this a useful thing? Then implement it.
        /// **Unimplemented**
        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shl(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl Numeric for $name {
            // TODO: decide if we want this.
            /// Return largest value that can be represented.
            /// **Not Implemented**
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self + rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            /// `self - rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            /// `self * rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            /// `self + rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                // TODO: this won't work vor matrices
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32` (coefficient-wise and wrapping).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].exp(exp)
                }
                out
            }

            /// **Not implemented**.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// `self / rhs` (coefficient-wise and wrapping).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].div(rhs[i])
                }
                out
            }
            /// **Not implemented**
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_signed_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature="use_attributes", primitive(hacspec))]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature="use_attributes", primitive(hacspec))]
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shr(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shl(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_unsigned_secret {
    ($name:ident) => {
        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add(self, rhs: $name) -> $name {
                debug_assert!(
                    self.len() == rhs.len(),
                    "Can't add two sequences that don't have the same length."
                );
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] + rhs[i]
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub(self, rhs: $name) -> $name {
                debug_assert!(
                    self.len() == rhs.len(),
                    "Can't add two sequences that don't have the same length."
                );
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] - rhs[i]
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul(self, rhs: $name) -> $name {
                debug_assert!(
                    self.len() == rhs.len(),
                    "Can't add two sequences that don't have the same length."
                );
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] * rhs[i]
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn rem(self, _rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitor(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i] ^ rhs[i]
                }
                out
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitand(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shr(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shl(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, _rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, _exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, _rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_signed_secret {
    ($name:ident) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature="use_attributes", primitive(hacspec))]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature="use_attributes", primitive(hacspec))]
            fn cmp(&self, other: &Self) -> Ordering {
                unimplemented!();
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shr(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn shl(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}
