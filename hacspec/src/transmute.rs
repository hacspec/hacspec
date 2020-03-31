use crate::prelude::*;

// U32

#[allow(non_snake_case)]
pub fn U32_to_le_bytes(x: U32) -> U32Word {
    U32Word::from(U32::to_bytes_le(&[x]))
}

#[allow(non_snake_case)]
pub fn U32_to_be_bytes(x: U32) -> U32Word {
    U32Word::from(U32::to_bytes_be(&[x]))
}

#[allow(non_snake_case)]
pub fn U32_from_be_bytes(s: U32Word) -> U32 {
    U32::from_bytes_be(&s.0)[0]
}

#[allow(non_snake_case)]
pub fn U32_from_le_bytes(s: U32Word) -> U32 {
    U32::from_bytes_le(&s.0)[0]
}

// U64

#[allow(non_snake_case)]
pub fn U64_to_le_bytes(x: U64) -> U64Word {
    U64Word::from(U64::to_bytes_le(&[x]))
}

#[allow(non_snake_case)]
pub fn U64_to_be_bytes(x: U64) -> U64Word {
    U64Word::from(U64::to_bytes_be(&[x]))
}

#[allow(non_snake_case)]
pub fn U64_from_be_bytes(s: U64Word) -> U64 {
    U64::from_bytes_be(&s.0)[0]
}

#[allow(non_snake_case)]
pub fn U64_from_le_bytes(s: U64Word) -> U64 {
    U64::from_bytes_le(&s.0)[0]
}

// U128

#[allow(non_snake_case)]
pub fn U128_to_le_bytes(x: U128) -> U128Word {
    U128Word::from(U128::to_bytes_le(&[x]))
}

#[allow(non_snake_case)]
pub fn U128_to_be_bytes(x: U128) -> U128Word {
    U128Word::from(U128::to_bytes_be(&[x]))
}

#[allow(non_snake_case)]
pub fn U128_from_be_bytes(s: U128Word) -> U128 {
    U128::from_bytes_be(&s.0)[0]
}

#[allow(non_snake_case)]
pub fn U128_from_le_bytes(s: U128Word) -> U128 {
    U128::from_bytes_le(&s.0)[0]
}

// u32

pub fn u32_to_le_bytes(x: u32) -> u32Word {
    u32Word::from(u32::to_le_bytes(x))
}

pub fn u32_to_be_bytes(x: u32) -> u32Word {
    u32Word::from(u32::to_be_bytes(x))
}

pub fn u32_from_be_bytes(s: u32Word) -> u32 {
    u32::from_be_bytes(s.0)
}

pub fn u32_from_le_bytes(s: u32Word) -> u32 {
    u32::from_le_bytes(s.0)
}

// u64

pub fn u64_to_le_bytes(x: u64) -> u64Word {
    u64Word::from(u64::to_le_bytes(x))
}

pub fn u64_to_be_bytes(x: u64) -> u64Word {
    u64Word::from(u64::to_be_bytes(x))
}

pub fn u64_from_be_bytes(s: u64Word) -> u64 {
    u64::from_be_bytes(s.0)
}

pub fn u64_from_le_bytes(s: u64Word) -> u64 {
    u64::from_le_bytes(s.0)
}

// u128

pub fn u128_to_le_bytes(x: u128) -> u128Word {
    u128Word::from(u128::to_le_bytes(x))
}

pub fn u128_to_be_bytes(x: u128) -> u128Word {
    u128Word::from(u128::to_be_bytes(x))
}

pub fn u128_from_be_bytes(s: u128Word) -> u128 {
    u128::from_be_bytes(s.0)
}

pub fn u128_from_le_bytes(s: u128Word) -> u128 {
    u128::from_le_bytes(s.0)
}
