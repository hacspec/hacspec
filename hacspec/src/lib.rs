//!
//! hacspec consists of three parts:
//! * hacspec library
//! * syntax checker
//! * compiler
//!
//! # The hacspec library
//!
//! The hacspec library implements a comprehensive set of functions to implement
//! succinct cryptographic specs that can be compiled to formal languages such
//! as [F*](https://www.fstar-lang.org/).
//!
//! # The syntax checker
//! TODO:
//! * describe clippy extension
//! * add `cargo hacspec check` command
//!
//! # The compiler
//! TODO:
//! * define compiler interface
//! * add `cargo hacspec fstar` command
//!

pub use rand;
use std::convert::AsMut;
use std::ops::{Index, IndexMut, Range, RangeFull};

pub mod array;
pub mod integer;
pub mod machine_integers;
pub mod math_integers;
pub mod numeric;
pub mod poly;
pub mod prelude;
pub mod public_seq;
pub mod seq;
pub mod test_vectors;
pub mod util;
pub mod vec_integers;

use crate::prelude::*;

// The following are only for documentation purposes.
bytes!(DocSecretBytes, 64);
public_bytes!(DocPublicBytes, 64);
array!(DocSecretArray, 64, U32);
array!(DocPublicArray, 64, u32);

/// Common trait for all byte arrays and sequences.
pub trait SeqTrait<T: Copy> {
    fn raw<'a>(&'a self) -> &'a [T];
    fn len(&self) -> usize;
    fn iter(&self) -> std::slice::Iter<T>;
    fn iter_mut(&mut self) -> std::slice::IterMut<T>;
}

bytes!(U32Word, 4);
bytes!(U128Word, 16);
bytes!(U64Word, 8);
array!(Counter, 2, usize);

array!(u32Word, 4, u8);
array!(u64Word, 8, u8);
array!(u128Word, 16, u8);

pub fn u32_to_le_bytes(x: U32) -> U32Word {
    U32Word([
        U8::from((x & U32::classify(0xFF000000u32)) >> 24),
        U8::from((x & U32::classify(0xFF0000u32)) >> 16),
        U8::from((x & U32::classify(0xFF00u32)) >> 8),
        U8::from(x & U32::classify(0xFFu32)),
    ])
}

pub fn u32_from_be_bytes(s: U32Word) -> U32 {
    U32::from_bytes_be(&s.0)[0]
}

pub fn u32_from_le_bytes(s: U32Word) -> U32 {
    U32::from_bytes_le(&s.0)[0]
}

pub fn u32_from_le_bytes_u32(s: u32Word) -> u32 {
    u32::from_le_bytes(s.0)
}

pub fn u32_to_be_bytes(x: U32) -> U32Word {
    U32Word::from(U32::to_bytes_be(&[x]))
}

pub fn u128_from_le_bytes(s: U128Word) -> U128 {
    U128::from_bytes_le(&s.0)[0]
}

pub fn u128_from_be_bytes(s: U128Word) -> U128 {
    U128::from_bytes_be(&s.0)[0]
}

pub fn u128_to_be_bytes(x: U128) -> U128Word {
    U128Word::from(U128::to_bytes_be(&[x]))
}

pub fn u64_to_be_bytes_u64(x: u64) -> u64Word {
    u64Word::from(u64::to_be_bytes(x))
}

pub fn u64_to_be_bytes(x: U64) -> U64Word {
    U64Word::from(U64::to_bytes_be(&[x]))
}

pub fn u64_to_le_bytes(x: U64) -> U64Word {
    U64Word::from(U64::to_bytes_le(&[x]))
}

#[macro_export]
macro_rules! secret_array {
    ( $int_type: ident, [ $( $x:expr ),+ ] ) => {
        [
            $(
                $int_type($x)
            ),+
        ]
    }
}

#[macro_export]
macro_rules! secret_bytes {
    ([ $( $x:expr ),+ ] ) => {
        secret_array!(U8, [$($x),+])
    }
}

#[macro_export]
macro_rules! assert_secret_array_eq {
    ( $a1: expr, $a2: expr, $si: ident) => {
        assert_eq!(
            $a1.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>(),
            $a2.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>()
        );
    };
}

#[macro_export]
macro_rules! assert_bytes_eq {
    ( $a1: expr, $a2: expr) => {
        assert_secret_array_eq!($a1, $a2, U8)
    };
}

#[macro_export]
macro_rules! unsigned_integer_old_public {
    ($name:ident, $bits:literal) => {
        define_abstract_integer_checked!($name, $bits);
    };
}

// #[macro_export]
// macro_rules! field_integer {
//     ($name:ident, $base:ident, $max:expr) => {
//         define_refined_modular_integer!($name, $base, $max);

//         impl $name {
//             pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> $name {
//                 $name::from_bytes_le(
//                     s.iter()
//                         .map(|x| U8::declassify(*x))
//                         .collect::<Vec<_>>()
//                         .as_slice(),
//                 )
//             }

//             pub fn to_byte_seq_le(self) -> Seq<U8> {
//                 Seq::from(
//                     self.to_bytes_le()
//                         .iter()
//                         .map(|x| U8::classify(*x))
//                         .collect::<Vec<U8>>(),
//                 )
//             }

//             pub fn from_secret_literal(x: U128) -> $name {
//                 $name::from_literal(U128::declassify(x))
//             }
//         }
//     };
// }

/// Compute ceil(a/b), returning a u64.
/// Note that float-uint conversion might be lossy.
pub fn div_ceil(a: usize, b: usize) -> u64 {
    (f64::ceil((a as f64) / (b as f64))) as u64
}
