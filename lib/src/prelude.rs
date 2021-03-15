//! This module conveniently exports common subroutines necessary for hacspecs
//!
//! ```
//! use hacspec_lib::prelude::*;
//! ```

pub use crate::array::*;
pub use crate::bigint_integers::*;
pub use crate::machine_integers::*;
pub use crate::math_integers::*;
pub use crate::math_util::{ct_util::*, *};
pub use crate::seq::*;
pub use crate::traits::*;
pub use crate::transmute::*;
pub use crate::util::*;
pub use crate::vec_integers::*;
pub use crate::vec_integers_public::*;
pub use crate::vec_integers_secret::*;
pub(crate) use crate::vec_util::*;
pub use crate::*;

pub use abstract_integers::*;
#[cfg(feature = "use_attributes")]
pub use hacspec_attributes::*;
pub use secret_integers::*;

pub use num::{self, traits::sign::Signed, BigUint, CheckedSub, Num, Zero};
pub use std::num::ParseIntError;
pub use std::ops::*;
pub use std::str::FromStr;
pub use std::{cmp::min, cmp::PartialEq, fmt, fmt::Debug};

bytes!(U16Word, 2);
bytes!(U32Word, 4);
bytes!(U64Word, 8);
bytes!(U128Word, 16);

public_bytes!(u16Word, 2);
public_bytes!(u32Word, 4);
public_bytes!(u64Word, 8);
public_bytes!(u128Word, 16);

// Re-export some std lib functions
pub use std::convert::TryFrom; // Allow down-casting of integers.
