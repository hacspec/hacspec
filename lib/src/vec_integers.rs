#![allow(unused_variables)]
///!
///! Implement the `Numeric` trait for arrays.
///!
use crate::prelude::*;

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_numeric_unsigned_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul(self, rhs: $name) -> $name {
                self.compatible(&rhs);
                vec_poly_mul(self, rhs, 0)
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shr(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        // TODO: is this a useful thing? Then implement it.
        /// **Unimplemented**
        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shl(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl ModNumeric for $name {
            /// `(self - rhs) % n` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).modulo(n)
            }
            /// `(self + rhs) % n` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).modulo(n)
            }
            /// `(self * rhs) % n` (coefficient-wise)
            /// Note that the multiplication is wrapping.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).modulo(n)
            }
            /// `(self ^ exp) % n` (coefficient-wise)
            /// Note that the exponentiation is wrapping.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_self(exp).modulo(n)
            }
            /// `self % n` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                self.compatible(&n);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].modulo(n[i])
                }
                out
            }
            /// `self % n` (coefficient-wise)
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                self
            }
        }
        impl Numeric for $name {
            // TODO: decide if we want this.
            /// Return largest value that can be represented.
            /// **Not Implemented**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self + rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            /// `self - rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            /// `self * rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            /// `self + rhs` (coefficient-wise and wrapping)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_div(self, rhs: Self) -> Self {
                // TODO: this won't work vor matrices
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32` (coefficient-wise and wrapping).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].exp(exp)
                }
                out
            }

            /// **Not implemented**.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// `self / rhs` (coefficient-wise and wrapping).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                self.compatible(&rhs);
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].div(rhs[i])
                }
                out
            }
            /// **Not implemented**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_numeric_signed_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shr(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shl(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            fn signed_modulo(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].absolute();
                }
                out
            }
        }
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_numeric_unsigned_secret {
    ($name:ident, $t:ty) => {
        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rem(self, _rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitor(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitand(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shr(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shl(self, _rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, _n: Self) -> Self {
                unimplemented!();
            }
            fn signed_modulo(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|` (coefficient-wise)
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                self
            }
        }
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_div(self, _rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, _exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, _rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, other: Self) -> bool {
                let mut result = <$t>::max_value();
                for (&a, &b) in self.iter().zip(other.iter()) {
                    result = result & a.equal_bm(b);
                }
                result.declassify() == <$t>::max_value().declassify()
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_numeric_signed_secret {
    ($name:ident) => {
        impl PartialOrd for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn cmp(&self, other: &Self) -> Ordering {
                unimplemented!();
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shr(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn shl(self, rhs: usize) -> Self::Output {
                unimplemented!();
            }
        }

        impl NumericCopy for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            fn signed_modulo(self, _n: Self) -> Self {
                unimplemented!();
            }
        }
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_mul<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].mul_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_mul(y[i]);
        }
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_add<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].add_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_add(y[i]);
        }
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_sub<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].sub_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_sub(y[i]);
        }
    }
    out
}

// /// Polynomial multiplication on ℤ[x]
// impl<T: Numeric> Mul for Seq<T> {
//     type Output = Self;
//     fn mul(self, rhs: Self) -> Self::Output {
//         Self {
//             b: poly_mul(&self.b, &rhs.b, T::default()),
//             idx: 0,
//         }
//     }
// }

// /// Polynomial subtraction on ℤ[x]
// impl<T: Numeric> Sub for Seq<T> {
//     type Output = Self;
//     fn sub(self, rhs: Self) -> Self::Output {
//         Self {
//             b: vec_poly_sub(&self.b, &rhs.b, T::default()),
//             idx: 0,
//         }
//     }
// }

// /// Polynomial addition on ℤ[x]
// impl<T: Numeric> Add for Seq<T> {
//     type Output = Self;
//     fn add(self, rhs: Self) -> Self::Output {
//         Self {
//             b: vec_poly_add(&self.b, &rhs.b, T::default()),
//             idx: 0,
//         }
//     }
// }
