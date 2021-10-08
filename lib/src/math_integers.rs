//! # Math Integers
//!
//! This module implements a number of different math integers.
//!
//! ## Integers
//!
//! * Unsigned Integers: `unsigned_integer`, `unsigned_public_integer`
//! * Signed Integers: `signed_integer`, `signed_public_integer`
//! * Natural Numbers modulo an integer: `nat_mod`, `public_nat_mod`
//!
//! ```
//! use hacspec_lib::prelude::*;
//! unsigned_integer!(LargeSecretInteger, 233);
//! let a = LargeSecretInteger::from_literal(1);
//! let b = LargeSecretInteger::from_literal(2);
//! let c = a + b;
//! let result = std::panic::catch_unwind(|| {
//!     // This panics because comparing secret math integers is currently not support.
//!     assert!(c.equal(LargeSecretInteger::from_literal(3)));
//! });
//! assert!(result.is_err());
//! let _max = LargeSecretInteger::from_hex("1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
//! ```

// TODO: Implement Integer for all math integers?

#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_public_integer!($name, $n);

        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_byte_seq_be<A: SeqTrait<U8>>(s: &A) -> $name {
                $name::from_be_bytes(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_public_byte_seq_be<A: SeqTrait<u8>>(s: A) -> $name {
                // XXX: unnecessarily complex
                $name::from_be_bytes(s.iter().map(|x| *x).collect::<Vec<_>>().as_slice())
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_byte_seq_be(self) -> Seq<U8> {
                Seq::from_vec(
                    self.to_be_bytes()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }
        }

        impl NumericCopy for $name {}
        impl UnsignedInteger for $name {}
        impl UnsignedIntegerCopy for $name {}
        impl Integer for $name {
            const NUM_BITS: usize = $n;

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn from_hex_string(s: &String) -> Self {
                Self::from_hex(&s.replace("0x", ""))
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
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs) % n
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
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp, n)
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
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                $name::max_value()
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
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into(), Self::max_val())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp.into(), Self::max_val())
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                $name::inv(self, n)
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
                self >= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                if !self.equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                if self.equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                if self.greater_than(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self.greater_than_or_qual(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                if self.less_than(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self.less_than_or_equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
        }
    };
}

#[macro_export]
macro_rules! signed_public_integer {
    ($name:ident,$n:literal) => {
        abstract_signed_public_integer!($name, $n);

        impl NumericCopy for $name {}
        impl ModNumeric for $name {
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
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp, n).signed_modulo(n)
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
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: implement in abstract-integers
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
                unimplemented!();
            }
        }
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                Self::max_value()
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
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into(), Self::max_val())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp, Self::max_val())
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                $name::inv(self, n)
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
                if !self.equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                if self.equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                if self.greater_than(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self.greater_than_or_qual(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                if self.less_than(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self.less_than_or_equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
        }
    };
}

#[macro_export]
macro_rules! unsigned_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_secret_integer!($name, $n);

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
macro_rules! signed_integer {
    ($name:ident,$n:literal) => {
        abstract_signed_secret_integer!($name, $n);

        impl NumericCopy for $name {}
        impl Integer for $name {
            const NUM_BITS: usize = $n;

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            /// Read hex string to `Self`.
            fn from_hex_string(s: &String) -> Self {
                let sign_str = if s.starts_with("-") { "-" } else { "+" };
                Self::from_hex(
                    &sign_str,
                    &s.replace("0x", "").replace("-", "").replace("+", ""),
                )
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
        impl ModNumeric for $name {
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
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n` that always returns a positive integer
            /// FIXME: implement ct
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: implement in abstract-integers
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn absolute(self) -> Self {
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
macro_rules! nat_mod {
    (type_name: $name:ident, type_of_canvas: $base:ident, bit_size_of_field: $bits:literal, modulo_value: $n:literal) => {
        abstract_nat_mod!($name, $base, $bits, $n);

        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> $name {
                $name::from_le_bytes(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_byte_seq_le(self) -> Seq<U8> {
                Seq::from_vec(
                    self.to_le_bytes()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }
        }

        impl NumericCopy for $name {}
        impl Integer for $name {
            const NUM_BITS: usize = $bits;

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn from_hex_string(s: &String) -> Self {
                Self::from_hex(&s.replace("0x", ""))
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
        impl UnsignedInteger for $name {}
        // XXX: Note that this is not actually doing anything. There's no public
        //      version.
        impl SecretInteger for $name {
            type PublicVersion = BigInt;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn classify(x: Self::PublicVersion) -> Self {
                unimplemented!();
            }
        }
        impl UnsignedSecretInteger for $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn to_le_bytes(self) -> Seq<U8> {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn to_be_bytes(self) -> Seq<U8> {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_le_bytes(x: &Seq<U8>) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_be_bytes(x: &Seq<U8>) -> Self {
                unimplemented!();
            }
        }
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                self - rhs
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                self + rhs
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                self * rhs
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn modulo(self, n: Self) -> Self {
                self.modulo(n)
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
                let bm = self.equal_bm(other);
                let bm: BigInt = bm.declassify();
                bm != BigInt::zero()
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than(self, other: Self) -> bool {
                let bm = self.greater_than_bm(other);
                let bm: BigInt = bm.declassify();
                bm != BigInt::zero()
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_qual(self, other: Self) -> bool {
                let bm = self.greater_than_or_equal_bm(other);
                let bm: BigInt = bm.declassify();
                bm != BigInt::zero()
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than(self, other: Self) -> bool {
                let bm = self.less_than_bm(other);
                let bm: BigInt = bm.declassify();
                bm != BigInt::zero()
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal(self, other: Self) -> bool {
                let bm = self.less_than_or_equal_bm(other);
                let bm: BigInt = bm.declassify();
                bm != BigInt::zero()
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

#[macro_export]
macro_rules! public_nat_mod {
    (type_name: $name:ident, type_of_canvas: $base:ident,  bit_size_of_field: $bits:literal, modulo_value: $n:literal) => {
        unsigned_public_integer!($base, $bits);
        abstract_public_modular_integer!($name, $base, $base::from_hex($n));

        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_byte_seq_be<A: SeqTrait<U8>>(s: &A) -> $name {
                $base::from_be_bytes(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
                .into()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_public_byte_seq_be<A: SeqTrait<u8>>(s: A) -> $name {
                $base::from_be_bytes(s.iter().map(|x| *x).collect::<Vec<_>>().as_slice()).into()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_byte_seq_be(self) -> Seq<U8> {
                Seq::from_vec(
                    self.to_be_bytes()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_public_byte_seq_be(self) -> Seq<u8> {
                Seq::from_vec(self.to_be_bytes())
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> $name {
                $base::from_le_bytes(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
                .into()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_public_byte_seq_le<A: SeqTrait<u8>>(s: A) -> $name {
                $base::from_le_bytes(s.iter().map(|x| *x).collect::<Vec<_>>().as_slice()).into()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_byte_seq_le(self) -> Seq<U8> {
                Seq::from_vec(
                    self.to_le_bytes()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_public_byte_seq_le(self) -> Seq<u8> {
                Seq::from_vec(self.to_le_bytes())
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn from_secret_literal(x: U128) -> $name {
                $base::from_literal(U128::declassify(x)).into()
            }
        }

        impl NumericCopy for $name {}
        impl UnsignedInteger for $name {}
        impl UnsignedIntegerCopy for $name {}
        impl Integer for $name {
            const NUM_BITS: usize = $bits;

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn from_hex_string(s: &String) -> Self {
                Self::from_hex(&s.replace("0x", ""))
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
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                self - rhs
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                self + rhs
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                self * rhs
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp)
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
        impl Numeric for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn max_val() -> Self {
                (Self::max() - $base::from_literal(1)).into()
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
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp)
            }
            /// Division.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            /// **NOTE:** `n` is ignored and inversion is done with respect to
            ///            the modulus.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn inv(self, n: Self) -> Self {
                self.inv()
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
            // Return $bits-1 1s as we can't represent 0xF..F.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not_equal_bm(self, other: Self) -> Self {
                if self != other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn equal_bm(self, other: Self) -> Self {
                if self == other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_bm(self, other: Self) -> Self {
                if self > other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self >= other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_bm(self, other: Self) -> Self {
                if self < other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self <= other {
                    (Self::ONE() << ($bits - 1)) - Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
        }
    };
}
