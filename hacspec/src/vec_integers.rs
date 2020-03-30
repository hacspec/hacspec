#![allow(unused_variables)]
///!
///! Implement the `Numeric` trait for arrays.
///!

use crate::prelude::*;

#[macro_export]
macro_rules! _implement_numeric_unsigned_public {
    ($name:ident) => {
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b.wrapping_add(c);
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b.wrapping_sub(c);
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                $name::from(vec_poly_mul(&self.0, &rhs.0, 0))
                // debug_assert!(self.len() == rhs.len());
                // if self.len() != rhs.len() {
                //     panic!("Can't add two sequences that don't have the same length.");
                // }
                // let mut out = Self::new();
                // for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                //     *a = b.wrapping_mul(c);
                // }
                // out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b / c;
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, _rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for (a, (b, c)) in out.0.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
                    *a = *b ^ *c;
                }
                out
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, _rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, _rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            fn wrap_div(self, _rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, _exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, _rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            fn equal(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
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
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
            fn add(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b + c;
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b - c;
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                debug_assert!(self.len() == rhs.len());
                if self.len() != rhs.len() {
                    panic!("Can't add two sequences that don't have the same length.");
                }
                let mut out = Self::new();
                for (a, (&b, &c)) in out.iter_mut().zip(self.iter().zip(rhs.iter())) {
                    *a = b * c;
                }
                out
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, _rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for (a, (b, c)) in out.0.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
                    *a = *b ^ *c;
                }
                out
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, _rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, _rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, _rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            fn wrap_div(self, _rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, _exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, _rhs: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, _rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            fn equal(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, _other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, _other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, _other: Self) -> Self {
                unimplemented!();
            }
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
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                unimplemented!();
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                unimplemented!();
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

// ==== Numeric and NumericVec implementations for PublicSeq and Seq ==== //

impl<T: Numeric> NumericBase for PublicSeq<T> {
    /// Return largest value that can be represented.
    fn max_val() -> Self {
        unimplemented!();
    }

    fn wrap_add(self, rhs: Self) -> Self {
        self + rhs
    }
    fn wrap_sub(self, rhs: Self) -> Self {
        self - rhs
    }
    fn wrap_mul(self, rhs: Self) -> Self {
        self * rhs
    }
    fn wrap_div(self, rhs: Self) -> Self {
        unimplemented!();
    }

    /// `self ^ exp` where `exp` is a `u32`.
    fn pow(self, exp: u32) -> Self {
        unimplemented!();
    }
    /// `self ^ exp` where `exp` is a `Self`.
    fn pow_self(self, exp: Self) -> Self {
        unimplemented!();
    }
    /// (self - rhs) % n.
    fn sub_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self ^ exp) % n`
    fn pow_mod(self, exp: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// Division.
    fn div(self, rhs: Self) -> Self {
        unimplemented!();
    }
    /// `self % n`
    fn rem(self, n: Self) -> Self {
        unimplemented!();
    }
    /// Invert self modulo n.
    fn inv(self, n: Self) -> Self {
        unimplemented!();
    }
    /// `|self|`
    fn abs(self) -> Self {
        unimplemented!();
    }

    // Comparison functions returning bool.
    fn equal(self, other: Self) -> bool {
        unimplemented!();
    }
    fn greater_than(self, other: Self) -> bool {
        unimplemented!();
    }
    fn greater_than_or_qual(self, other: Self) -> bool {
        unimplemented!();
    }
    fn less_than(self, other: Self) -> bool {
        unimplemented!();
    }
    fn less_than_or_equal(self, other: Self) -> bool {
        unimplemented!();
    }

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    fn not_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn greater_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn greater_than_or_qual_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn less_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn less_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
}

#[inline]
pub fn vec_poly_mul<T: Numeric>(x: &[T], y: &[T], n: T) -> Vec<T> {
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        if !n.equal(T::default()) {
            *a = b.mul_mod(c, n);
        } else {
            *a = b.wrap_mul(c);
        }
    }
    out
}

#[inline]
pub fn vec_poly_add<T: Numeric>(x: &[T], y: &[T], n: T) -> Vec<T> {
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        if !n.equal(T::default()) {
            *a = b.add_mod(c, n);
        } else {
            *a = b.wrap_add(c);
        }
    }
    out
}

#[inline]
pub fn vec_poly_sub<T: Numeric>(x: &[T], y: &[T], n: T) -> Vec<T> {
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        if !n.equal(T::default()) {
            *a = b.sub_mod(c, n);
        } else {
            *a = b.wrap_sub(c);
        }
    }
    out
}

/// Polynomial multiplication on ℤ[x]
impl<T: Numeric> Mul for PublicSeq<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            b: vec_poly_mul(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial subtraction on ℤ[x]
impl<T: Numeric> Sub for PublicSeq<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            b: vec_poly_sub(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial addition on ℤ[x]
impl<T: Numeric> Add for PublicSeq<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            b: vec_poly_add(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

impl<T: Numeric> Not for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn not(self) -> Self::Output {
        unimplemented!();
    }
}

impl<T: Numeric> BitOr for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn bitor(self, rhs: Self) -> Self::Output {
        unimplemented!();
    }
}

impl<T: Numeric> BitXor for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut out = Self::default();
        for (a, (b, c)) in out.b.iter_mut().zip(self.b.iter().zip(rhs.b.iter())) {
            *a = *b ^ *c;
        }
        out
    }
}

impl<T: Numeric> BitAnd for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn bitand(self, rhs: Self) -> Self::Output {
        unimplemented!();
    }
}

impl<T: Numeric> Shr<u32> for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn shr(self, rhs: u32) -> Self::Output {
        unimplemented!();
    }
}

impl<T: Numeric> Shl<u32> for PublicSeq<T> {
    type Output = PublicSeq<T>;
    fn shl(self, rhs: u32) -> Self::Output {
        unimplemented!();
    }
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
