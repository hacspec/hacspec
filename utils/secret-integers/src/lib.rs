//! This crate defines simple wrappers around Rust's integer type to guarantee they are used in
//! a constant-time fashion. Hence, division and direct comparison of these "secret" integers is
//! disallowed.
//!
//! These integers are intended to be the go-to type to use when implementing cryptographic
//! software, as they provide an extra automated check against use of variable-time operations.
//!
//! To use the crate, just import everything (`use secret_integers::*;`) and replace your integer
//! types with uppercase versions of their names (e.g. `u8` -> `U8`).
//!
//! # Examples
//!
//! In order to print information or test code involving your secret integers, you need first to
//! declassify them. Your crypto code should not contain any `declassify` occurence though to
//! guarantee constant-timedness. Make sure to specify the type of your literals when classifying
//! (e.g. `0x36u16`) or else you'll get a casting error.
//!
//! ```
//! # use secret_integers::*;
//! let x = U32::classify(1u32);
//! let y : U32 = 2u32.into();
//! assert_eq!((x + y).declassify(), 3);
//! ```
//!
//! Using an illegal operation will get you a compile-time error:
//!
//! ```compile_fail
//! # use secret_integers::*;
//! let x = U32::classify(4u32);
//! let y : U32 = 2u32.into();
//! assert_eq!((x / y).declassify(), 2);
//! ```
//!
//! Since indexing arrays and vectors is only possible with `usize`, these secret integers also
//! prevent you from using secret values to index memory (which is a breach to constant-timedness
//! due to cache behaviour).
//!
//! ```
//! # use secret_integers::*;
//! fn xor_block(block1: &mut [U64;16], block2: &[U64;16]) {
//!    for i in 0..16 {
//!      block1[i] ^= block2[i]
//!    }
//! }
//! ```
//! See the [Dalek](https://github.com/denismerigoux/rust-secret-integers/tree/master/examples/dalek.rs)
//! and [Chacha20](https://github.com/denismerigoux/rust-secret-integers/tree/master/examples/chacha20.rs)
//! examples for more details on how to use this crate.
//!
//!
//! # Const-compatibility
//!
//! Because stable Rust does not allow constant functions for now, it is impossible to use those
//! wrappers in const declarations. Even classifying directly inside the declaration does not work:
//!
//! ```compile_fail
//! const IV : [U32;2] = [U32::classify(0xbe6548u32),U32::classify(0xaec6d48u32)]
//! ```
//!
//! For now, the solution is to map your const items with `classify` once you're inside a function,
//! or call `into`.
//!
//! ```
//! # use secret_integers::*;
//! const IV : [u32;2] = [0xbe6548, 0xaec6d48];
//!
//! fn start_cipher(plain: &mut Vec<U32>) {
//!    for i in 0..plain.len() {
//!      plain[i] = plain[i] | (plain[i] ^ IV[i].into());
//!    }
//! }
//! ```
//!

#![no_std]

extern crate alloc;
use alloc::vec::Vec;

use core::num::Wrapping;
use core::ops::*;

macro_rules! define_wrapping_op {
    ($name:ident, $op:tt, $op_name:ident, $func_op:ident, $assign_name:ident, $assign_func:ident, $checked_func_op:ident) => {

        /// **Warning:** has wrapping semantics.
        impl $op_name for $name {
            type Output = Self;
            #[inline]
            fn $func_op(self, rhs: Self) -> Self {
                let $name(i1) = self;
                let $name(i2) = rhs;
                $name((Wrapping(i1) $op Wrapping(i2)).0)
            }
        }

        impl $name {
            /// **Warning:** panics when overflow.
            pub fn $checked_func_op(self, rhs: Self) -> Self {
                let $name(i1) = self;
                let $name(i2) = rhs;
                match i1.$checked_func_op(i2) {
                    None => panic!("Secret integer {} overflow!", stringify!($func_op)),
                    Some(r) => $name(r)
                }
            }
        }

        /// **Warning:** has wrapping semantics.
        impl $assign_name for $name {
            #[inline]
            fn $assign_func(&mut self, rhs: Self) {
                *self = *self $op rhs
            }
        }
    }
}

macro_rules! define_bitwise_op {
    ($name:ident, $op:tt, $op_name:ident, $func_op:ident, $assign_name:ident, $assign_func:ident) => {
        impl $op_name for $name {
            type Output = Self;
            #[inline]
            fn $func_op(self, rhs: Self) -> Self {
                let $name(i1) = self;
                let $name(i2) = rhs;
                $name(i1 $op i2)
            }
        }

        impl $assign_name for $name {
            #[inline]
            fn $assign_func(&mut self, rhs: Self) {
                *self = *self $op rhs
            }
        }
    }
}

macro_rules! define_unary_op {
    ($name:ident, $op:tt, $op_name:ident, $func_op:ident) => {
        impl $op_name for $name {
            type Output = Self;
            #[inline]
            fn $func_op(self) -> Self {
                let $name(i1) = self;
                $name($op i1)
            }
        }
    }
}

macro_rules! define_shift {
    ($name:ident, $op:tt, $wrapop:ident, $op_name:ident, $func_op:ident, $assign_name:ident, $assign_func:ident) => {
        impl $op_name<usize> for $name {
            type Output = Self;
            #[inline]
            fn $func_op(self, rhs: usize) -> Self {
                let $name(i1) = self;
                $name(i1.$wrapop(rhs as u32))
            }
        }

        impl $assign_name<usize> for $name {
            #[inline]
            fn $assign_func(&mut self, rhs: usize) {
                *self = *self $op rhs
            }
        }
    }
}

macro_rules! define_secret_integer {
    ($name:ident, $repr:ty, $bits:tt) => {
        #[derive(Clone, Copy, Default)]
        pub struct $name(pub $repr);

        impl $name {
            #[inline]
            pub fn classify<T : Into<$repr>>(x: T) -> Self {
                $name(x.into())
            }

            #[inline]
            /// **Warning:** use with caution, breaks the constant-time guarantee.
            pub fn declassify(self) -> $repr {
                self.0
            }

            #[inline]
            pub fn zero() -> Self {
                $name(0)
            }

            #[inline]
            pub fn one() -> Self {
                $name(1)
            }

            #[inline]
            pub fn ones() -> Self {
                !Self::zero()
            }

            pub fn from_le_bytes(bytes: &[U8]) -> Vec<$name> {
                assert!(bytes.len() % ($bits/8) == 0);
                bytes.chunks($bits/8).map(|chunk| {
                    let mut chunk_raw : [u8; $bits/8] = [0u8; $bits/8];
                    for i in 0..$bits/8 {
                        chunk_raw[i] = U8::declassify(chunk[i]);
                    }
                    $name::classify(unsafe {
                        core::mem::transmute::<[u8;$bits/8], $repr>(
                            chunk_raw
                        ).to_le()
                    })
                }).collect::<Vec<$name>>()
            }

            pub fn to_le_bytes(ints: &[$name]) -> Vec<U8> {
                ints.iter().map(|int| {
                    let int = $name::declassify(*int);
                    let bytes : [u8;$bits/8] = unsafe {
                         core::mem::transmute::<$repr, [u8;$bits/8]>(int.to_le())
                    };
                    let secret_bytes : Vec<U8> = bytes.iter().map(|x| U8::classify(*x)).collect();
                    secret_bytes
                }).flatten().collect()
            }

            pub fn from_be_bytes(bytes: &[U8]) -> Vec<$name> {
                assert!(bytes.len() % ($bits/8) == 0);
                bytes.chunks($bits/8).map(|chunk| {
                    let mut chunk_raw : [u8; $bits/8] = [0u8; $bits/8];
                    for i in 0..$bits/8 {
                        chunk_raw[i] = U8::declassify(chunk[i]);
                    }
                    $name::classify(unsafe {
                        core::mem::transmute::<[u8;$bits/8], $repr>(
                            chunk_raw
                        ).to_be()
                    })
                }).collect::<Vec<$name>>()
            }

            pub fn to_be_bytes(ints: &[$name]) -> Vec<U8> {
                ints.iter().map(|int| {
                    let int = $name::declassify(*int);
                    let bytes : [u8;$bits/8] = unsafe {
                         core::mem::transmute::<$repr, [u8;$bits/8]>(int.to_be())
                    };
                    let secret_bytes : Vec<U8> = bytes.iter().map(|x| U8::classify(*x)).collect();
                    secret_bytes
                }).flatten().collect()
            }

            pub fn max_value() -> $name {
                $name::classify(<$repr>::max_value())
            }
        }

        impl From<$repr> for $name {
            #[inline]
            fn from(x:$repr) -> Self {
                Self::classify(x)
            }
        }

        define_wrapping_op!($name, +, Add, add, AddAssign, add_assign, checked_add);
        define_wrapping_op!($name, -, Sub, sub, SubAssign, sub_assign, checked_sub);
        define_wrapping_op!($name, *, Mul, mul, MulAssign, mul_assign, checked_mul);

        define_shift!($name, <<, wrapping_shl, Shl, shl, ShlAssign, shl_assign);
        define_shift!($name, >>, wrapping_shr, Shr, shr, ShrAssign, shr_assign);

        impl $name {
            #[inline]
            pub fn rotate_left(self, rotval:usize) -> Self {
                let $name(i) = self;
                $name(i.rotate_left(rotval as u32))
            }

            #[inline]
            pub fn rotate_right(self, rotval:usize) -> Self {
                let $name(i) = self;
                $name(i.rotate_right(rotval as u32))
            }
        }

        define_bitwise_op!($name, &, BitAnd, bitand, BitAndAssign, bitand_assign);
        define_bitwise_op!($name, |, BitOr, bitor, BitOrAssign, bitor_assign);
        define_bitwise_op!($name, ^, BitXor, bitxor, BitXorAssign, bitxor_assign);

        // `Not` has bitwise semantics for integers
        define_unary_op!($name, !, Not, not);

        // Printing integers.
        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                let uint: $repr = self.declassify();
                write!(f, "{}", uint)
            }
        }
        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                let uint: $repr = self.declassify();
                write!(f, "{}", uint)
            }
        }
        impl core::fmt::LowerHex for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                let val: $repr = self.declassify();
                core::fmt::LowerHex::fmt(&val, f)
            }
        }
        // impl Distribution<$name> for Standard {
        //     fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $name {
        //         $name(rng.gen())
        //     }
        // }
    }
}

macro_rules! define_secret_unsigned_integer {
    ($name:ident, $repr:ty, $bits:tt) => {
        // Secret unsigned integer.
        define_secret_integer!($name, $repr, $bits);
        impl Neg for $name {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self {
                let $name(i1) = self;
                $name((Wrapping(!i1) + Wrapping(1)).0)
            }
        }

        /// # Constant-time comparison operators
        impl $name {
            /// Produces a new integer which is all ones if the two arguments are equal and
            /// all zeroes otherwise. With inspiration from
            /// [Wireguard](https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=2e60bb395c1f589a398ec606d611132ef9ef764b).
            #[inline]
            pub fn comp_eq(self, rhs: Self) -> Self {
                let a = self;
                let b = rhs;
                let x = a ^ b;
                let minus_x = -x;
                let x_or_minus_x = x | minus_x;
                let xnx = x_or_minus_x >> ($bits - 1);
                let c = xnx - Self::one();
                c
            }

            /// Produces a new integer which is all ones if the first argument is different from
            /// the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_ne(self, rhs: Self) -> Self {
                !self.comp_eq(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is greater than or
            /// equal to the second argument, and all zeroes otherwise. With inspiration from
            /// [WireGuard](https://git.zx2c4.com/WireGuard/commit/src/crypto/curve25519-hacl64.h?id=0a483a9b431d87eca1b275463c632f8d5551978a).
            #[inline]
            pub fn comp_gte(self, rhs: Self) -> Self {
                let x = self;
                let y = rhs;
                let x_xor_y = x ^ y;
                let x_sub_y = x - y;
                let x_sub_y_xor_y = x_sub_y ^ y;
                let q = x_xor_y | x_sub_y_xor_y;
                let x_xor_q = x ^ q;
                let x_xor_q_ = x_xor_q >> ($bits - 1);
                let c = x_xor_q_ - Self::one();
                c
            }

            /// Produces a new integer which is all ones if the first argument is strictly greater
            /// than the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_gt(self, rhs: Self) -> Self {
                self.comp_gte(rhs) ^ self.comp_eq(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is less than or
            /// equal to the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_lte(self, rhs: Self) -> Self {
                !self.comp_gt(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is strictly less than
            /// the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_lt(self, rhs: Self) -> Self {
                !self.comp_gte(rhs)
            }
        }
    };
}

macro_rules! define_secret_signed_integer {
    ($name:ident, $repr:ty, $bits:tt) => {
        // Secret signed integer.
        define_secret_integer!($name, $repr, $bits);
        define_unary_op!($name, -, Neg, neg);

        /// # Constant-time comparison operators
        impl $name {
            #[inline]
            pub fn comp_eq(self, rhs: Self) -> Self {
                !self.comp_ne(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is different from
            /// the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_ne(self, rhs: Self) -> Self {
                let x = (self - rhs) | (rhs - self);
                x >> ($bits - 1)
            }

            /// Produces a new integer which is all ones if the first argument is greater than or
            /// equal to the second argument, and all zeroes otherwise. With inspiration from
            #[inline]
            pub fn comp_gte(self, rhs: Self) -> Self {
                self.comp_gt(rhs) | self.comp_eq(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is strictly greater
            /// than the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_gt(self, rhs: Self) -> Self {
                !self.comp_lt(rhs) & !self.comp_eq(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is less than or
            /// equal to the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_lte(self, rhs: Self) -> Self {
                self.comp_lt(rhs) | self.comp_eq(rhs)
            }

            /// Produces a new integer which is all ones if the first argument is strictly less than
            /// the second argument, and all zeroes otherwise.
            #[inline]
            pub fn comp_lt(self, rhs: Self) -> Self {
                let d = self - rhs;
                let x = self ^ ((self ^ d) & (rhs ^ d));
                x >> ($bits - 1)
            }
        }
    }
}

define_secret_unsigned_integer!(U8, u8, 8);
define_secret_unsigned_integer!(U16, u16, 16);
define_secret_unsigned_integer!(U32, u32, 32);
define_secret_unsigned_integer!(U64, u64, 64);
define_secret_unsigned_integer!(U128, u128, 128);
define_secret_signed_integer!(I8, i8, 8);
define_secret_signed_integer!(I16, i16, 16);
define_secret_signed_integer!(I32, i32, 32);
define_secret_signed_integer!(I64, i64, 64);
define_secret_signed_integer!(I128, i128, 128);

macro_rules! define_uU_casting {
    ($from:ident, $to:ident, $to_repr:ident, $func_name: ident) => {
        impl From<$from> for $to {
            #[inline]
            fn from(x: $from) -> $to {
                $to(<$to_repr>::from(x))
            }
        }

        #[inline]
        #[allow(non_snake_case)]
        pub fn $func_name(x: $from) -> $to {
            $to(<$to_repr>::from(x))
        }
    };
}

macro_rules! define_usize_casting {
    ($from:ident, $to:ident, $to_repr:ident, $func_name: ident) => {
        impl From<$from> for $to {
            #[inline]
            fn from(x: $from) -> $to {
                $to(x as $to_repr)
            }
        }

        #[inline]
        #[allow(non_snake_case)]
        pub fn $func_name(x: $from) -> $to {
            $to(x as $to_repr)
        }
    };
}

macro_rules! define_Uu_casting {
    ($from:ident, $to:ident, $func_name: ident) => {
        /// **Warning:** conversion can be lossy!
        impl From<$from> for $to {
            #[inline]
            fn from(x: $from) -> $to {
                <$to>::from(x.declassify())
            }
        }

        /// **Warning:** conversion can be lossy!
        #[inline]
        #[allow(non_snake_case)]
        pub fn $func_name(x: $from) -> $to {
            <$to>::from(x.declassify())
        }
    };
}

macro_rules! define_safe_casting {
    ($from:ident, $to:ident, $to_repr:ident, $func_name: ident) => {
        impl From<$from> for $to {
            #[inline]
            fn from(x: $from) -> $to {
                $to(x.0 as $to_repr)
            }
        }

        #[inline]
        #[allow(non_snake_case)]
        pub fn $func_name(x: $from) -> $to {
            $to(x.0 as $to_repr)
        }
    };
}

macro_rules! define_unsafe_casting {
    ($from:ident, $to:ident, $to_repr:ident, $func_name: ident) => {
        /// **Warning:** wrapping semantics.
        impl From<$from> for $to {
            #[inline]
            fn from(x: $from) -> $to {
                $to(x.0 as $to_repr)
            }
        }

        /// **Warning:** wrapping semantics.
        #[inline]
        #[allow(non_snake_case)]
        pub fn $func_name(x: $from) -> $to {
            $to(x.0 as $to_repr)
        }
    };
}

macro_rules! define_signed_unsigned_casting {
    ($unsigned:ident, $unsigned_repr:ident, $signed:ident, $signed_repr:ident) => {
        /// **Warning:** wrapping semantics.
        impl From<$unsigned> for $signed {
            #[inline]
            fn from(x: $unsigned) -> $signed {
                $signed(x.0 as $signed_repr)
            }
        }

        impl From<$signed> for $unsigned {
            #[inline]
            fn from(x: $signed) -> $unsigned {
                $unsigned(x.0 as $unsigned_repr)
            }
        }
    };
}

// Casting

// U128 <-> Un{n < 128}
define_safe_casting!(U8, U128, u128, U128_from_U8);
define_unsafe_casting!(U128, U8, u8, U8_from_U128);
define_safe_casting!(U16, U128, u128, U128_from_U16);
define_unsafe_casting!(U128, U16, u16, U16_from_U128);
define_safe_casting!(U32, U128, u128, U128_from_U32);
define_unsafe_casting!(U128, U32, u32, U32_from_U128);
define_safe_casting!(U64, U128, u128, U128_from_U64);
define_unsafe_casting!(U128, U64, u64, U64_from_U128);

// U64 <-> Un{n < 64}
define_safe_casting!(U8, U64, u64, U64_from_U8);
define_unsafe_casting!(U64, U8, u8, U8_from_U64);
define_safe_casting!(U16, U64, u64, U64_from_U16);
define_unsafe_casting!(U64, U16, u16, U16_from_U64);
define_safe_casting!(U32, U64, u64, U64_from_U32);
define_unsafe_casting!(U64, U32, u32, U32_from_U64);

// U32 <-> Un{n < 32}
define_safe_casting!(U8, U32, u32, U32_from_U8);
define_unsafe_casting!(U32, U8, u8, U8_from_U32);
define_safe_casting!(U16, U32, u32, U32_from_U16);
define_unsafe_casting!(U32, U16, u16, U16_from_U32);

// U16 <-> Un{n < 16}
define_safe_casting!(U8, U16, u16, U16_from_U8);
define_unsafe_casting!(U16, U8, u8, U8_from_U16);

// U8 <-> u
define_Uu_casting!(U8, u8, declassify_u8_from_U8);
define_Uu_casting!(U8, u16, declassify_u16_from_U8);
define_Uu_casting!(U8, u32, declassify_u32_from_U8);
define_Uu_casting!(U8, u64, declassify_u64_from_U8);
define_Uu_casting!(U8, u128, declassify_u128_from_U8);
define_Uu_casting!(U8, usize, declassify_usize_from_U8);
define_usize_casting!(usize, U8, u8, U8_from_usize);

// U16 <-> u
define_Uu_casting!(U16, u16, declassify_u16_from_U16);
define_Uu_casting!(U16, u32, declassify_u32_from_U16);
define_Uu_casting!(U16, u64, declassify_u64_from_U16);
define_Uu_casting!(U16, u128, u128_from_U16);

// U32 <-> u
define_Uu_casting!(U32, u32, declassify_u32_from_U32);
define_Uu_casting!(U32, u64, declassify_u64_from_U32);
define_Uu_casting!(U32, u128, declassify_u128_from_U32);

// U64 <-> u
define_Uu_casting!(U64, u64, declassify_u64_from_U64);
define_Uu_casting!(U64, u128, declassify_u128_from_U64);

// U128 <-> u
define_Uu_casting!(U128, u128, declassify_u128_from_U128);

// u16 <-> U
define_uU_casting!(u8, U16, u16, u8_from_U16);

// u32 <-> U
define_uU_casting!(u8, U32, u32, u8_from_U32);
define_uU_casting!(u16, U32, u32, u16_from_U32);

// u64 <-> U
define_uU_casting!(u8, U64, u64, u8_from_U64);
define_uU_casting!(u16, U64, u64, u16_from_U64);
define_uU_casting!(u32, U64, u64, u32_from_U64);
define_usize_casting!(usize, U64, u64, U64_from_usize);

// u128 <-> U
define_uU_casting!(u8, U128, u128, u8_from_U128);
define_uU_casting!(u16, U128, u128, u16_from_U128);
define_uU_casting!(u32, U128, u128, u32_from_U128);
define_uU_casting!(u64, U128, u128, u64_from_U128);
define_usize_casting!(usize, U128, u128, U128_from_usize);

// I128 <-> In{n < 128}
define_safe_casting!(I8, I128, i128, I128_from_I8);
define_unsafe_casting!(I128, I8, i8, I8_from_I128);
define_safe_casting!(I16, I128, i128, I128_from_I16);
define_unsafe_casting!(I128, I16, i16, I16_from_I128);
define_safe_casting!(I32, I128, i128, I128_from_I32);
define_unsafe_casting!(I128, I32, i32, I32_from_I128);
define_safe_casting!(I64, I128, i128, I128_from_I64);
define_unsafe_casting!(I128, I64, i64, I64_from_I128);

// I64 <-> In{n < 64}
define_safe_casting!(I8, I64, i64, I64_from_I8);
define_unsafe_casting!(I64, I8, i8, I8_from_I64);
define_safe_casting!(I16, I64, i64, I64_from_I16);
define_unsafe_casting!(I64, I16, i16, I16_from_I64);
define_safe_casting!(I32, I64, i64, I64_from_I32);
define_unsafe_casting!(I64, I32, i32, I32_from_I64);

// I32 <-> In{n < 32}
define_safe_casting!(I8, I32, i32, I32_from_I8);
define_unsafe_casting!(I32, I8, i8, I8_from_I32);
define_safe_casting!(I16, I32, i32, I32_from_I16);
define_unsafe_casting!(I32, I16, i16, I16_from_I32);

// I16 <-> In{n < 16}
define_safe_casting!(I8, I16, i16, I16_from_I8);
define_unsafe_casting!(I16, I8, i8, I8_from_I16);

// Unsigned <-> signed
define_signed_unsigned_casting!(U128, u128, I128, i128);
define_signed_unsigned_casting!(U64, u64, I64, i64);
define_signed_unsigned_casting!(U32, u32, I32, i32);
define_signed_unsigned_casting!(U16, u16, I16, i16);
define_signed_unsigned_casting!(U8, u8, I8, i8);
