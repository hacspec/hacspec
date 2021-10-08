#![allow(non_snake_case)]

use crate::prelude::*;

// U32

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U16_to_le_bytes(x: U16) -> U16Word {
    U16Word::from_vec(U16::to_le_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U16_to_be_bytes(x: U16) -> U16Word {
    U16Word::from_vec(U16::to_be_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U16_from_be_bytes(s: U16Word) -> U16 {
    U16::from_be_bytes(&s.0)[0]
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U16_from_le_bytes(s: U16Word) -> U16 {
    U16::from_le_bytes(&s.0)[0]
}

// U32

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U32_to_le_bytes(x: U32) -> U32Word {
    U32Word::from_vec(U32::to_le_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U32_to_be_bytes(x: U32) -> U32Word {
    U32Word::from_vec(U32::to_be_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U32_from_be_bytes(s: U32Word) -> U32 {
    U32::from_be_bytes(&s.0)[0]
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U32_from_le_bytes(s: U32Word) -> U32 {
    U32::from_le_bytes(&s.0)[0]
}

// U64

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U64_to_le_bytes(x: U64) -> U64Word {
    U64Word::from_vec(U64::to_le_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U64_to_be_bytes(x: U64) -> U64Word {
    U64Word::from_vec(U64::to_be_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U64_from_be_bytes(s: U64Word) -> U64 {
    U64::from_be_bytes(&s.0)[0]
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U64_from_le_bytes(s: U64Word) -> U64 {
    U64::from_le_bytes(&s.0)[0]
}

// U128

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U128_to_le_bytes(x: U128) -> U128Word {
    U128Word::from_vec(U128::to_le_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U128_to_be_bytes(x: U128) -> U128Word {
    U128Word::from_vec(U128::to_be_bytes(&[x]))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U128_from_be_bytes(s: U128Word) -> U128 {
    U128::from_be_bytes(&s.0)[0]
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn U128_from_le_bytes(s: U128Word) -> U128 {
    U128::from_le_bytes(&s.0)[0]
}

// u16

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u16_to_le_bytes(x: u16) -> u16Word {
    u16Word::from_array(u16::to_le_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u16_to_be_bytes(x: u16) -> u16Word {
    u16Word::from_array(u16::to_be_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u16_from_be_bytes(s: u16Word) -> u16 {
    u16::from_be_bytes(s.0)
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u16_from_le_bytes(s: u16Word) -> u16 {
    u16::from_le_bytes(s.0)
}

// u32

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u32_to_le_bytes(x: u32) -> u32Word {
    u32Word::from_array(u32::to_le_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u32_to_be_bytes(x: u32) -> u32Word {
    u32Word::from_array(u32::to_be_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u32_from_be_bytes(s: u32Word) -> u32 {
    u32::from_be_bytes(s.0)
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u32_from_le_bytes(s: u32Word) -> u32 {
    u32::from_le_bytes(s.0)
}

// u64

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u64_to_le_bytes(x: u64) -> u64Word {
    u64Word::from_array(u64::to_le_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u64_to_be_bytes(x: u64) -> u64Word {
    u64Word::from_array(u64::to_be_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u64_from_be_bytes(s: u64Word) -> u64 {
    u64::from_be_bytes(s.0)
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u64_from_le_bytes(s: u64Word) -> u64 {
    u64::from_le_bytes(s.0)
}

// u128

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u128_to_le_bytes(x: u128) -> u128Word {
    u128Word::from_array(u128::to_le_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u128_to_be_bytes(x: u128) -> u128Word {
    u128Word::from_array(u128::to_be_bytes(x))
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u128_from_be_bytes(s: u128Word) -> u128 {
    u128::from_be_bytes(s.0)
}

#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn u128_from_le_bytes(s: u128Word) -> u128 {
    u128::from_le_bytes(s.0)
}
