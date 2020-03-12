//! This crate defines specification-friendly natural integers with an upper bound. Operations on
//! these integers can be defined as modular (modulo the upper bound) or regular (with a panic
//! on underflow or overflow).
//!
//! As each integer gets its own Rust type, the compiler detects and prevent any mixing between
//! all the diffent integers you would have defined.
//!
//! # Defining a new integer type
//!
//! Here is the macro used to defined the `SizeNatExample` type of this crate:
//!
//! ```ignore
//! define_abstract_integer_checked!(SizeNatExample, 64);
//! ```
//!
//! `SizeNat` is the name of the newly-created type. `64` is the number of bits of the machine
//! representation of the type. From the number of bits is derived an upper bound for the integer
//! for which all operations are checked for overflow.
//!
//! The resulting integer type is copyable, and supports addition, substraction, multiplication,
//! integer division, remainder, comparison and equality. The `from_literal` method allows you to
//! convert integer literals into your new type.
//!
//! # Refining an integer type for modular arithmetic
//!
//! On top of a previously defined abstract integer, you can define another type that lets you
//! implement modular arithmetic. For instance, this crate defines the arithmetic field over the
//! 9th Mersenne prime with:
//!
//! ```ignore
//! define_refined_modular_integer!(
//!    SizeNatFieldExample,
//!    SizeNatExample,
//!    SizeNatExample::pow2(61) - SizeNatExample::from_literal(1)
//! );
//! ```
//!
//! The first argument of this new macro is the name of the newly defined refined type. The second
//! argument is the name of the base abstract integer that will act as the representation. The
//! third example is the modulo for all operations, defined as a value of the base type.
//!
//!
//! # Example
//!
//! ```
//! # use num::BigUint;
//! # use abstract_integers::*;
//! let x1 = SizeNatExample::from_literal(687165654266415);
//! let x2 = SizeNatExample::from_literal(4298832000156);
//! let x3 = x1 + x2;
//! assert_eq!(SizeNatExample::from_literal(691464486266571), x3);
//! let x4 = SizeNatExample::from_literal(8151084996540);
//! let x5 = x3 - x4;
//! assert_eq!(SizeNatExample::from_literal(683313401270031), x5.into());
//! let x6 = x5 / SizeNatExample::from_literal(1541654268);
//! assert_eq!(SizeNatExample::from_literal(443233), x6.into());
//! let x7 : SizeNatFieldExample = SizeNatFieldExample::from_literal(2305843009213693951) + x6.into();
//! assert_eq!(x7, x6.into());
//! ```
//!

extern crate num;
#[allow(unused_imports)]
use num::{BigUint, CheckedSub, Zero};
use std::num::ParseIntError;
use std::ops::*;

/// Defines a bounded natural integer with regular arithmetic operations, checked for overflow
/// and underflow.
#[macro_export]
macro_rules! define_abstract_integer_checked {
    ($name:ident, $bits:literal) => {
        #[derive(Clone, Copy)]
        pub struct $name([u8; ($bits + 7) / 8]);

        impl Default for $name {
            fn default() -> $name {
                $name([0u8; ($bits + 7) / 8])
            }
        }

        impl From<BigUint> for $name {
            fn from(x: BigUint) -> $name {
                let max_value = BigUint::from(1u32) <<  $bits;
                assert!(x < max_value, "BigUint {} is too big x for type {}!", x, stringify!($name));
                let repr = x.to_bytes_be();
                if repr.len() > ($bits + 7) / 8 {
                    panic!("BigUint {} too big for type {}", x, stringify!($name))
                }
                let mut out = [0u8; ($bits + 7) / 8];
                let upper = out.len();
                let lower = upper - repr.len();
                out[lower..upper].copy_from_slice(&repr);
                $name(out)
            }
        }

        impl Into<BigUint> for $name {
            fn into(self) -> BigUint {
                BigUint::from_bytes_be(&self.0)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigUint = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigUint = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl $name {
            fn max() -> BigUint {
                BigUint::from(2u32).shl($bits)
            }

            fn hex_string_to_bytes(s: &str) -> Vec<u8> {
                assert!(s.len() % 2 == 0, "length of hex string {}: {}",s, s.len());
                let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
                    .collect();
                b.expect("Error parsing hex string")
            }

            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                BigUint::from_bytes_be(&Self::hex_string_to_bytes(s)).into()
            }

            #[allow(dead_code)]
            pub fn from_bytes_le(v: &[u8]) -> Self {
                BigUint::from_bytes_le(v).into()
            }

            #[allow(dead_code)]
            pub fn to_bytes_le(self) -> Vec<u8> {
                BigUint::to_bytes_le(&self.into())
            }

            #[allow(dead_code)]
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigUint::from(x);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }

            #[allow(dead_code)]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigUint::from(x as u128);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a + b;
                if c > $name::max() {
                    panic!("bounded addition overflow for type {}", stringify!($name));
                }
                c.into()
            }
        }

        /// **Warning**: panics on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a.checked_sub(&b).unwrap_or_else(|| {
                    panic!(
                        "bounded substraction underflow for type {}",
                        stringify!($name)
                    )
                });
                c.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a * b;
                if c > $name::max() {
                    panic!(
                        "bounded multiplication overflow for type {}",
                        stringify!($name)
                    );
                }
                c.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                if b == BigUint::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a / b;
                c.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                if b == BigUint::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a % b;
                c.into()
            }
        }

        impl PartialEq for $name {
            fn eq(&self, rhs: &$name) -> bool {
                let a: BigUint = (*self).into();
                let b: BigUint = (*rhs).into();
                a == b
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &$name) -> Option<std::cmp::Ordering> {
                let a: BigUint = (*self).into();
                let b: BigUint = (*other).into();
                a.partial_cmp(&b)
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl $name {
            /// Returns 2 to the power of the argument
            #[allow(dead_code)]
            pub fn pow2(x: usize) -> $name {
                BigUint::from(1u32).shl(x).into()
            }

            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            pub fn bit(self, i: usize) -> bool {
                assert!(
                    i < self.0.len() * 8,
                    "the bit queried should be lower than the size of the integer representation: {} < {}",
                    i,
                    self.0.len() * 8
                );
                let bigint : BigUint = self.into();
                let tmp: BigUint = bigint >> i;
                (tmp & BigUint::from(1u128)).to_bytes_le()[0] == 1
            }

            #[allow(dead_code)]
            pub fn inv(self, modval: Self) -> Self {
                let biguintmodval : BigUint = modval.into();
                let m = &biguintmodval - BigUint::from(2u32);
                let s: BigUint = (self).into();
                s.modpow(&m, &biguintmodval).into()
            }

            #[allow(dead_code)]
            pub fn pow_felem(self, exp: Self, modval: Self) -> Self {
                let a: BigUint = self.into();
                let b: BigUint = exp.into();
                let m: BigUint = modval.into();
                let c: BigUint = a.modpow(&b, &m);
                c.into()
            }
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u128, modval: Self) -> Self {
                self.pow_felem(BigUint::from(exp).into(), modval)
            }
        }
    };
}

/// Defines a bounded natural integer with modular arithmetic operations
#[macro_export]
macro_rules! define_refined_modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
        pub struct $name($base);

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: $base = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: $base = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl $name {
            pub fn max() -> $base {
                $max
            }

            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                $base::from_hex(s).into()
            }

            #[allow(dead_code)]
            pub fn inv(self) -> Self {
                let base: $base = self.into();
                base.inv(Self::max()).into()
            }

            #[allow(dead_code)]
            pub fn pow_felem(self, exp: Self) -> Self {
                let base: $base = self.into();
                base.pow_felem(exp.into(), Self::max()).into()
            }
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u128) -> Self {
                let base: $base = self.into();
                base.pow(exp, Self::max()).into()
            }

            #[allow(dead_code)]
            pub fn from_bytes_le(v: &[u8]) -> Self {
                $base::from_bytes_le(v).into()
            }

            #[allow(dead_code)]
            pub fn to_bytes_le(self) -> Vec<u8> {
                $base::to_bytes_le(self.into())
            }

            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            pub fn bit(self, i: usize) -> bool {
                $base::bit(self.into(), i)
            }

            #[allow(dead_code)]
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigUint::from(x);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                $name(big_x.into())
            }

            #[allow(dead_code)]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigUint::from(x as u128);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                $name(big_x.into())
            }
        }

        impl From<$base> for $name {
            fn from(x: $base) -> $name {
                $name(x % $max)
            }
        }

        impl Into<$base> for $name {
            fn into(self) -> $base {
                self.0
            }
        }

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a + b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let max: BigUint = $max.into();
                let c: BigUint = if b > a { max.clone() - b + a } else { a - b };
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a * b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a / b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a % b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }
    };
}

// Natural integer bounded by std::usize::MAX
define_abstract_integer_checked!(SizeNatExample, 64);

define_refined_modular_integer!(
    SizeNatFieldExample,
    SizeNatExample,
    SizeNatExample::pow2(61) - SizeNatExample::from_literal(1)
);

mod tests;
