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
pub mod transmute;

use crate::prelude::*;

// The following are only for documentation purposes.
bytes!(DocSecretBytes, 64);
public_bytes!(DocPublicBytes, 64);
array!(DocSecretArray, 64, U32);
array!(DocPublicArray, 64, u32);

/// Common trait for all byte arrays and sequences.
pub trait SeqTrait<T: Copy> {
    fn len(&self) -> usize;
    fn iter(&self) -> std::slice::Iter<T>;
}

bytes!(U32Word, 4);
bytes!(U128Word, 16);
bytes!(U64Word, 8);
array!(Counter, 2, usize);

array!(u32Word, 4, u8);
array!(u64Word, 8, u8);
array!(u128Word, 16, u8);


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
