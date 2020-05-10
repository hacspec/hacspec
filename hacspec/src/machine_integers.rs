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

macro_rules! implement_public_unsigned_mi {
    ($t:ty,$bits:literal) => {
        implement_public_mi!($t, $bits, <$t>::max_val());
        impl ModNumeric for $t {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                let mut tmp = self;
                while tmp < rhs {
                    tmp += n;
                }
                (tmp - rhs) % n
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs) % n
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs) % n
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self
            }
        }
    };
}

macro_rules! implement_public_signed_mi {
    ($t:ty,$bits:literal) => {
        implement_public_mi!($t, $bits, -1);
        impl ModNumeric for $t {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).signed_modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).signed_modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).signed_modulo(n)
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::ZERO()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self.abs()
            }
        }
    };
}

// Macro to implement the Numeric trait for built-in machine integers.
macro_rules! implement_public_mi {
    ($t:ty,$bits:literal,$true_val:expr) => {
        impl Numeric for $t {}
        impl Integer for $t {
            const NUM_BITS: u32 = $bits;
            
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ZERO() -> Self {
                0
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ONE() -> Self {
                1
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn TWO() -> Self {
                2
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_literal(val: u128) -> Self {
                val as $t
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_hex_string(s: &String) -> Self {
                <$t>::from_str_radix(s.trim_start_matches("0x"), 16).unwrap()
            }
        }
        impl NumericBase for $t {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn max_val() -> Self {
                <$t>::max_value()
            }

            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self.wrapping_add(rhs)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self.wrapping_sub(rhs)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self.wrapping_mul(rhs)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                self.wrapping_div(rhs)
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp)
            }
            /// `self ^ exp` where `exp` is a `Self`.
            /// **XXX: Not implemented for public machine integers**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                extended_euclid_invert(self, n, false)
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                self == other
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                self <= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                if self != other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                if self == other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                if self > other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self >= other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                if self < other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self <= other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
        }
    };
}

implement_public_unsigned_mi!(u8, 8);
implement_public_unsigned_mi!(u16, 16);
implement_public_unsigned_mi!(u32, 32);
implement_public_unsigned_mi!(u64, 64);
implement_public_unsigned_mi!(u128, 128);

implement_public_signed_mi!(i8, 8);
implement_public_signed_mi!(i16, 16);
implement_public_signed_mi!(i32, 32);
implement_public_signed_mi!(i64, 64);
implement_public_signed_mi!(i128, 128);

// ========== Secret Machine Integers ========== //

macro_rules! implement_secret_unsigned_mi {
    ($t:ident,$base:ty,$bits:literal) => {
        implement_secret_mi!($t, $base, $bits);
        impl ModNumeric for $t {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).modulo(n)
            }
            /// `(self ^ exp) % n`
            /// TODO: implement
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                ct_div(self, n).1
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self
            }
        }
    };
}

macro_rules! implement_secret_signed_mi {
    ($t:ident,$base:ty,$bits:literal) => {
        implement_secret_mi!($t, $base, $bits);
        impl ModNumeric for $t {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).signed_modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).signed_modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).signed_modulo(n)
            }
            /// `(self ^ exp) % n`
            /// TODO: implement
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                ct_div(self, n).1
            }
            /// `self % n` that always returns a positive integer
            /// FIXME: not ct!
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::ZERO()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: Check if `abs` is ct
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                Self(self.declassify().abs())
            }
        }
    };
}

// Macro to implement the Numeric trait for secret machine integers.
macro_rules! implement_secret_mi {
    ($t:ident,$base:ty,$bits:literal) => {
        impl Numeric for $t {}
        impl Integer for $t {
            const NUM_BITS: u32 = $bits;

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ZERO() -> Self {
                $t(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ONE() -> Self {
                $t(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn TWO() -> Self {
                $t(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_literal(val: u128) -> Self {
                Self::classify(val as $base)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_hex_string(s: &String) -> Self {
                Self::classify(<$base>::from_str_radix(s.trim_start_matches("0x"), 16).unwrap())
            }
        }
        impl NumericBase for $t {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn max_val() -> Self {
                Self::from(<$base>::max_value())
            }

            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn wrap_div(self, _rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            /// **Note:** the exponent `exp` MUST NOT be secret.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                let mut s = self;
                if exp == 0 {
                    return <$t>::from(1 as $base);
                } else {
                    for _ in 1..exp {
                        s = s * self
                    }
                }
                Self::from(s)
            }
            /// `self ^ exp` where `exp` is a `Self`.
            /// Here both, base and exponent, are secret.
            /// TODO: implement
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                ct_div(self, rhs).0
            }
            /// Invert self modulo n.
            /// FIXME: make ct
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                extended_euclid_invert(self, n, false)
            }

            // Comparison functions returning bool.
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                self.equal_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                self.greater_than_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self.greater_than_or_equal_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                self.less_than_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                self.less_than_or_equal_bm(other).declassify() != 0
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                self.comp_ne(other)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                self.comp_eq(other)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                self.comp_gt(other)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                self.comp_gte(other)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                self.comp_lt(other)
            }
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                self.comp_lte(other)
            }
        }
    };
}

implement_secret_unsigned_mi!(U8, u8, 8);
implement_secret_unsigned_mi!(U16, u16, 16);
implement_secret_unsigned_mi!(U32, u32, 32);
implement_secret_unsigned_mi!(U64, u64, 64);
implement_secret_unsigned_mi!(U128, u128, 128);

implement_secret_signed_mi!(I8, i8, 8);
implement_secret_signed_mi!(I16, i16, 16);
implement_secret_signed_mi!(I32, i32, 32);
implement_secret_signed_mi!(I64, i64, 64);
implement_secret_signed_mi!(I128, i128, 128);
