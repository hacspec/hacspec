//!
//! This module implements the `Numeric` trait for machine integers.
//!
//! # Public Machine Integers
//! Public machine integers are `u8, i8, u16, i16, u32, i32, u64, i64, u128, i128`.
//!
//! # Secret Machine Integers
//! Secret machine integers are `U8, I8, U16, I16, U32, I32, U64, I64, U128, I128`.
//!

use crate::alloc::string::ToString;
use crate::math_util::{ct_util::*, *};
use crate::prelude::*;

macro_rules! implement_public_unsigned_mi {
    ($t:ty,$bits:literal) => {
        implement_public_mi!($t, $bits, <$t>::max_val());
        impl ModNumeric for $t {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                let mut tmp = self;
                while tmp < rhs {
                    tmp += n;
                }
                (tmp - rhs) % n
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs) % n
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs) % n
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).signed_modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).signed_modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).signed_modulo(n)
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                let r_big = BigInt::from(self).modpow(&BigInt::from(exp), &BigInt::from(n));
                debug_assert!(r_big <= BigInt::from(Self::max_val()));
                let r_string = r_big.to_string();
                r_string.parse().unwrap()
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::ZERO()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                self.abs()
            }
        }
    };
}

// Macro to implement the Numeric trait for built-in machine integers.
macro_rules! implement_public_mi {
    ($t:ty,$bits:literal,$true_val:expr) => {
        impl NumericCopy for $t {}
        impl Integer for $t {
            const NUM_BITS: usize = $bits;
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                0
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                1
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                2
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                val as $t
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn from_hex_string(s: &String) -> Self {
                <$t>::from_str_radix(s.trim_start_matches("0x"), 16).unwrap()
            }

            /// Get bit `i` of this integer.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn get_bit(self, i: usize) -> Self {
                (self >> i) & Self::ONE()
            }

            /// Set bit `i` of this integer to `b` and return the result.
            /// Bit `b` has to be `0` or `1`.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn set_bit(self, b: Self, i: usize) -> Self {
                debug_assert!(b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO()));
                let tmp1 = Self::from_literal(!(1 << i));
                let tmp2 = b << i;
                (self & tmp1) | tmp2
            }

            /// Set bit `pos` of this integer to bit `yi` of integer `y`.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn set(self, pos: usize, y: Self, yi: usize) -> Self {
                let b = y.get_bit(yi);
                self.set_bit(b, pos)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rotate_left(self, n: usize) -> Self {
                // Taken from https://blog.regehr.org/archives/1063
                assert!(n < Self::NUM_BITS);
                (self.clone() << n) | (self >> ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rotate_right(self, n: usize) -> Self {
                // Taken from https://blog.regehr.org/archives/1063
                assert!(n < Self::NUM_BITS);
                (self.clone() >> n) | (self << ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
            }
        }
        impl Numeric for $t {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                <$t>::max_value()
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_add(self, rhs: Self) -> Self {
                self.wrapping_add(rhs)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_sub(self, rhs: Self) -> Self {
                self.wrapping_sub(rhs)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_mul(self, rhs: Self) -> Self {
                self.wrapping_mul(rhs)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn wrap_div(self, rhs: Self) -> Self {
                self.wrapping_div(rhs)
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp)
            }
            /// `self ^ exp` where `exp` is a `Self`.
            /// **XXX: Not implemented for public machine integers**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                extended_euclid_invert(self, n, false)
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, other: Self) -> bool {
                self == other
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, other: Self) -> bool {
                self <= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                if self != other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                if self == other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                if self > other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self >= other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                if self < other {
                    $true_val
                } else {
                    <$t>::default()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).modulo(n)
            }
            /// `(self ^ exp) % n`
            /// TODO: implement
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                ct_div(self, n).1
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).signed_modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).signed_modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).signed_modulo(n)
            }
            /// `(self ^ exp) % n`
            /// TODO: implement
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, _exp: Self, _n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                ct_div(self, n).1
            }
            /// `self % n` that always returns a positive integer
            /// FIXME: not ct!
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::ZERO()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: Check if `abs` is ct
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                Self(self.declassify().abs())
            }
        }
    };
}

// Macro to implement the Numeric trait for secret machine integers.
macro_rules! implement_secret_mi {
    ($t:ident,$base:ty,$bits:literal) => {
        impl NumericCopy for $t {}
        impl Integer for $t {
            const NUM_BITS: usize = $bits;

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                $t(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                $t(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                $t(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                Self::classify(val as $base)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn from_hex_string(s: &String) -> Self {
                Self::classify(<$base>::from_str_radix(s.trim_start_matches("0x"), 16).unwrap())
            }

            /// Get bit `i` of this integer.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn get_bit(self, i: usize) -> Self {
                (self >> i) & Self::ONE()
            }

            /// Set bit `i` of this integer to `b` and return the result.
            /// Bit `b` has to be `0` or `1`.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn set_bit(self, b: Self, i: usize) -> Self {
                debug_assert!(b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO()));
                let tmp1 = Self::from_literal(!(1 << i));
                let tmp2 = b << i;
                (self & tmp1) | tmp2
            }

            /// Set bit `pos` of this integer to bit `yi` of integer `y`.
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn set(self, pos: usize, y: Self, yi: usize) -> Self {
                let b = y.get_bit(yi);
                self.set_bit(b, pos)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rotate_left(self, n: usize) -> Self {
                // Taken from https://blog.regehr.org/archives/1063
                assert!(n < Self::NUM_BITS);
                (self.clone() << n) | (self >> ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn rotate_right(self, n: usize) -> Self {
                // Taken from https://blog.regehr.org/archives/1063
                assert!(n < Self::NUM_BITS);
                (self.clone() >> n) | (self << ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
            }
        }
        impl Numeric for $t {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                Self::from(<$base>::max_value())
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
            /// **Note:** the exponent `exp` MUST NOT be secret.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, _exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                ct_div(self, rhs).0
            }
            /// Invert self modulo n.
            /// FIXME: make ct
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                extended_euclid_invert(self, n, false)
            }

            // Comparison functions returning bool.
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal(self, other: Self) -> bool {
                self.equal_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, other: Self) -> bool {
                self.greater_than_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self.greater_than_or_equal_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, other: Self) -> bool {
                self.less_than_bm(other).declassify() != 0
            }
            /// **Declassifies**
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, other: Self) -> bool {
                self.less_than_or_equal_bm(other).declassify() != 0
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                self.comp_ne(other)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                self.comp_eq(other)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                self.comp_gt(other)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                self.comp_gte(other)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                self.comp_lt(other)
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
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

impl UnsignedPublicInteger for u8 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<u8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<u8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
}

impl UnsignedPublicInteger for u16 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u16_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u16_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u16_from_le_bytes(u16Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u16_from_be_bytes(u16Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u32 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u32_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u32_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u32_from_le_bytes(u32Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u32_from_be_bytes(u32Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u64 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u64_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u64_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u64_from_le_bytes(u64Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u64_from_be_bytes(u64Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u128 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u128_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u128_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u128_from_le_bytes(u128Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u128_from_be_bytes(u128Word::from_seq(x))
    }
}

impl UnsignedInteger for U8 {}
impl UnsignedInteger for U16 {}
impl UnsignedInteger for U32 {}
impl UnsignedInteger for U64 {}
impl UnsignedInteger for U128 {}
impl UnsignedInteger for u8 {}
impl UnsignedInteger for u16 {}
impl UnsignedInteger for u32 {}
impl UnsignedInteger for u64 {}
impl UnsignedInteger for u128 {}

impl UnsignedIntegerCopy for U8 {}
impl UnsignedIntegerCopy for U16 {}
impl UnsignedIntegerCopy for U32 {}
impl UnsignedIntegerCopy for U64 {}
impl UnsignedIntegerCopy for U128 {}
impl UnsignedIntegerCopy for u8 {}
impl UnsignedIntegerCopy for u16 {}
impl UnsignedIntegerCopy for u32 {}
impl UnsignedIntegerCopy for u64 {}
impl UnsignedIntegerCopy for u128 {}

impl UnsignedSecretIntegerCopy for U8 {}
impl UnsignedSecretIntegerCopy for U16 {}
impl UnsignedSecretIntegerCopy for U32 {}
impl UnsignedSecretIntegerCopy for U64 {}
impl UnsignedSecretIntegerCopy for U128 {}
impl UnsignedPublicIntegerCopy for u8 {}
impl UnsignedPublicIntegerCopy for u16 {}
impl UnsignedPublicIntegerCopy for u32 {}
impl UnsignedPublicIntegerCopy for u64 {}
impl UnsignedPublicIntegerCopy for u128 {}

impl SignedInteger for I8 {}
impl SignedInteger for I16 {}
impl SignedInteger for I32 {}
impl SignedInteger for I64 {}
impl SignedInteger for I128 {}
impl SignedInteger for i8 {}
impl SignedInteger for i16 {}
impl SignedInteger for i32 {}
impl SignedInteger for i64 {}
impl SignedInteger for i128 {}

impl SignedIntegerCopy for I8 {}
impl SignedIntegerCopy for I16 {}
impl SignedIntegerCopy for I32 {}
impl SignedIntegerCopy for I64 {}
impl SignedIntegerCopy for I128 {}
impl SignedIntegerCopy for i8 {}
impl SignedIntegerCopy for i16 {}
impl SignedIntegerCopy for i32 {}
impl SignedIntegerCopy for i64 {}
impl SignedIntegerCopy for i128 {}

impl SecretIntegerCopy for I8 {
    type PublicVersionCopy = i8;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for I16 {
    type PublicVersionCopy = i16;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for I32 {
    type PublicVersionCopy = i32;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for I64 {
    type PublicVersionCopy = i64;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for I128 {
    type PublicVersionCopy = i128;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}

impl SecretIntegerCopy for U8 {
    type PublicVersionCopy = u8;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for U16 {
    type PublicVersionCopy = u16;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for U32 {
    type PublicVersionCopy = u32;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for U64 {
    type PublicVersionCopy = u64;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}
impl SecretIntegerCopy for U128 {
    type PublicVersionCopy = u128;
    fn classify(x: Self::PublicVersionCopy) -> Self {
        Self(x)
    }
}

impl PublicIntegerCopy for i8 {
    type SecretVersionCopy = I8;
}
impl PublicIntegerCopy for i16 {
    type SecretVersionCopy = I16;
}
impl PublicIntegerCopy for i32 {
    type SecretVersionCopy = I32;
}
impl PublicIntegerCopy for i64 {
    type SecretVersionCopy = I64;
}
impl PublicIntegerCopy for i128 {
    type SecretVersionCopy = I128;
}

impl PublicIntegerCopy for u8 {
    type SecretVersionCopy = U8;
}
impl PublicIntegerCopy for u16 {
    type SecretVersionCopy = U16;
}
impl PublicIntegerCopy for u32 {
    type SecretVersionCopy = u32;
}
impl PublicIntegerCopy for u64 {
    type SecretVersionCopy = I64;
}
impl PublicIntegerCopy for u128 {
    type SecretVersionCopy = I128;
}

impl PublicInteger for u8 {
    type SecretVersion = U8;
}
impl PublicInteger for u16 {
    type SecretVersion = U16;
}
impl PublicInteger for u32 {
    type SecretVersion = U32;
}
impl PublicInteger for u64 {
    type SecretVersion = U64;
}
impl PublicInteger for u128 {
    type SecretVersion = U128;
}
impl PublicInteger for i8 {
    type SecretVersion = I8;
}
impl PublicInteger for i16 {
    type SecretVersion = I16;
}
impl PublicInteger for i32 {
    type SecretVersion = I32;
}
impl PublicInteger for i64 {
    type SecretVersion = I64;
}
impl PublicInteger for i128 {
    type SecretVersion = I128;
}

impl SecretInteger for U8 {
    type PublicVersion = u8;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        U8(x)
    }
}
impl SecretInteger for U16 {
    type PublicVersion = u16;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        U16(x)
    }
}
impl SecretInteger for U32 {
    type PublicVersion = u32;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        U32(x)
    }
}
impl SecretInteger for U64 {
    type PublicVersion = u64;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        U64(x)
    }
}
impl SecretInteger for U128 {
    type PublicVersion = u128;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        U128(x)
    }
}
impl SecretInteger for I8 {
    type PublicVersion = i8;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        I8(x)
    }
}
impl SecretInteger for I16 {
    type PublicVersion = i16;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        I16(x)
    }
}
impl SecretInteger for I32 {
    type PublicVersion = i32;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        I32(x)
    }
}
impl SecretInteger for I64 {
    type PublicVersion = i64;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        I64(x)
    }
}
impl SecretInteger for I128 {
    type PublicVersion = i128;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn classify(x: Self::PublicVersion) -> Self {
        I128(x)
    }
}

impl UnsignedSecretInteger for U8 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<U8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<U8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
}

impl UnsignedSecretInteger for U16 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U16_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U16_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U16_from_le_bytes(U16Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U16_from_be_bytes(U16Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U32 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U32_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U32_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U32_from_le_bytes(U32Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U32_from_be_bytes(U32Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U64 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U64_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U64_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U64_from_le_bytes(U64Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U64_from_be_bytes(U64Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U128 {
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U128_to_le_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U128_to_be_bytes(self))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U128_from_le_bytes(U128Word::from_seq(x))
    }
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U128_from_be_bytes(U128Word::from_seq(x))
    }
}
