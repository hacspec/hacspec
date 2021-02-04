//!
//! Utility functions for hacspec internally.
//!

#[cfg(feature = "use_attributes")]
use crate::prelude::*;
use core::num::ParseIntError;

use alloc::vec::Vec;

#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub fn hex_string_to_bytes(s: &str) -> Vec<u8> {
    debug_assert!(s.len() % 2 == 0);
    let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect();
    b.expect("Error parsing hex string")
}

#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub fn to_array<A, T>(slice: &[T]) -> A
where
    A: Default + AsMut<[T]>,
    T: Copy,
{
    let mut a = A::default();
    <A as AsMut<[T]>>::as_mut(&mut a).copy_from_slice(slice);
    a
}
