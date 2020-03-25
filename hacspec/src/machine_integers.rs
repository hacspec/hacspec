//!
//! This module implements the `Numeric` trait for machine integers.
//!
//! # Public Machine Integers
//! Public machine integers are `u8, i8, u16, i16, u32, i32, u64, i64, u128, i128`.
//!
//! # Secret Machine Integers
//! Secret machine integers are `U8, I8, U16, I16, U32, I32, U64, I64, U128, I128`.
//!

use crate::prelude::*;
use crate::numeric::Numeric;

// Macro to implement the Numeric trait for built-in machine integers.
macro_rules! implement_public_mi {
    ($t:ty) => {
        impl Numeric for $t {}
        impl NumericBase for $t {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                <$t>::max_value()
            }

            fn wrap_add(self, rhs: Self) -> Self {
                self.wrapping_add(rhs)
            }
            fn wrap_sub(self, rhs: Self) -> Self {
                self.wrapping_sub(rhs)
            }
            fn wrap_mul(self, rhs: Self) -> Self {
                self.wrapping_mul(rhs)
            }
            fn wrap_div(self, rhs: Self) -> Self {
                self.wrapping_div(rhs)
            }
        
            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                self.pow(exp)
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs) % n
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs) % n
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self{
                (self * rhs) % n
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                self / rhs
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                self % n
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
            fn equal(self, other: Self) -> bool {
                self == other
            }
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                self <= other
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                if self != other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
            fn equal_bm(self, other: Self) -> Self {
                if self == other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
            fn greater_than_bm(self, other: Self) -> Self {
                if self > other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                if self >= other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
            fn less_than_bm(self, other: Self) -> Self {
                if self < other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self <= other {
                    <$t>::max_value()
                } else {
                    <$t>::default()
                }
            }
        }
    };
}

implement_public_mi!(u8);
implement_public_mi!(u16);
implement_public_mi!(u32);
implement_public_mi!(u64);
implement_public_mi!(u128);

implement_public_mi!(i8);
implement_public_mi!(i16);
implement_public_mi!(i32);
implement_public_mi!(i64);
implement_public_mi!(i128);


// FIXME: This is currently NOT constant time! Implement the underlying algorithms in secret integer.
// Macro to implement the Numeric trait for secret machine integers.
macro_rules! implement_secret_mi {
    ($t:ty,$base:ty) => {
        impl Numeric for $t {}
        impl NumericBase for $t {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                Self::from(<$base>::max_value())
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
                let s = <$t>::declassify(self);
                Self::from(s.pow(exp))
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(rhs);
                let n = <$t>::declassify(n);
                Self::from((s - o) % n)
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(rhs);
                let n = <$t>::declassify(n);
                Self::from((s + o) % n)
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self{
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(rhs);
                let n = <$t>::declassify(n);
                Self::from((s * o) % n)
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            fn div(self, rhs: Self) -> Self {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(rhs);
                Self::from(s / o)
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                let s = <$t>::declassify(self);
                let n = <$t>::declassify(n);
                Self::from(s % n)
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
            fn equal(self, other: Self) -> bool {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(other);
                s == o
            }
            fn greater_than(self, other: Self) -> bool {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(other);
                s > o
            }
            fn greater_than_or_qual(self, other: Self) -> bool {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(other);
                s >= o
            }
            fn less_than(self, other: Self) -> bool {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(other);
                s < o
            }
            fn less_than_or_equal(self, other: Self) -> bool {
                let s = <$t>::declassify(self);
                let o = <$t>::declassify(other);
                s <= o
            }
        
            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self {
                self.comp_ne(other)
            }
            fn equal_bm(self, other: Self) -> Self {
                self.comp_eq(other)
            }
            fn greater_than_bm(self, other: Self) -> Self {
                self.comp_gt(other)
            }
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                self.comp_gte(other)
            }
            fn less_than_bm(self, other: Self) -> Self {
                self.comp_lt(other)
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                self.comp_lte(other)
            }
        }
    };
}

implement_secret_mi!(U8, u8);
implement_secret_mi!(U16, u16);
implement_secret_mi!(U32, u32);
implement_secret_mi!(U64, u64);
implement_secret_mi!(U128, u128);

// FIXME: requires code in secret integers for constant-time comparison
implement_secret_mi!(I8, i8);
implement_secret_mi!(I16, i16);
implement_secret_mi!(I32, i32);
implement_secret_mi!(I64, i64);
implement_secret_mi!(I128, i128);
