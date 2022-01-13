//! # Efficient and safe bytes
//!
//! [`Bytes`] can be used when secret byte sequences ([`ByteSeq`]) are used but
//! they are too slow for using hacspec in a release version that interacts with
//! other Rust code, i.e. requires a lot conversions between [`U8`] and [`u8`].
#![allow(non_snake_case, dead_code)]

use super::*;

#[cfg(feature = "release")]
pub type Byte = u8;
#[cfg(not(feature = "release"))]
pub type Byte = U8;

#[cfg(feature = "release")]
pub type DoubleByte = u16;
#[cfg(not(feature = "release"))]
pub type DoubleByte = U16;

#[cfg(feature = "release")]
pub type QuadByte = u32;
#[cfg(not(feature = "release"))]
pub type QuadByte = U32;

#[cfg(feature = "release")]
pub type Bytes = PublicSeq<Byte>;
#[cfg(not(feature = "release"))]
pub type Bytes = Seq<Byte>;

#[cfg(feature = "release")]
#[macro_export]
macro_rules! create_bytes {
    ($( $b:expr ),+) => {
        Bytes::from_vec(
            vec![
                $(
                    $b
                ),+
            ]
        )
    };
}

#[cfg(not(feature = "release"))]
#[macro_export]
macro_rules! create_bytes {
    ($( $b:expr ),+) => {
        Bytes::from_vec(
            vec![
                $(
                    U8($b)
                ),+
            ]
        )
    };
}

impl PublicSeq<u8> {
    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_public_slice(v: &[u8]) -> PublicSeq<u8> {
        Self { b: v.to_vec() }
    }

    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_native(b: Vec<u8>) -> PublicSeq<u8> {
        Self { b }
    }

    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn to_native(&self) -> Vec<u8> {
        self.b.clone()
    }

    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn into_native(self) -> Vec<u8> {
        self.b
    }

    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn as_slice(&self) -> &[u8] {
        self.b.as_slice()
    }
}

impl Seq<U8> {
    #[inline(always)]
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_native(b: Vec<u8>) -> Self {
        Self::from_public_slice(&b)
    }

    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn as_slice(&self) -> Vec<u8> {
        self.to_native()
    }
}

#[cfg(feature = "release")]
#[inline(always)]
pub fn Byte(x: u8) -> Byte {
    x
}

#[cfg(not(feature = "release"))]
#[inline(always)]
pub fn Byte(x: u8) -> Byte {
    U8(x)
}

pub trait ByteTrait {
    fn declassify(self) -> u8;
}

impl ByteTrait for u8 {
    #[inline(always)]
    fn declassify(self) -> u8 {
        self
    }
}

#[inline(always)]
pub fn declassify_usize_from_U8(x: Byte) -> usize {
    x.into()
}

// === FIXME: NOT BYTES ANYMORE - MOVE ===

pub trait U16Trait {
    fn into_bytes(self) -> Bytes;
}
impl U16Trait for u16 {
    #[cfg(feature = "release")]
    fn into_bytes(self) -> Bytes {
        Bytes::from_native_slice(&u16::to_be_bytes(self))
    }
    #[cfg(not(feature = "release"))]
    fn into_bytes(self) -> Bytes {
        Bytes::from_seq(&U16_to_be_bytes(U16(self)))
    }
}
#[cfg(not(feature = "release"))]
impl U16Trait for U16 {
    fn into_bytes(self) -> Bytes {
        Bytes::from_seq(&U16_to_be_bytes(self))
    }
}

pub trait U32Trait {
    fn into_bytes(self) -> Bytes;
}

impl U32Trait for u32 {
    #[cfg(feature = "release")]
    fn into_bytes(self) -> Bytes {
        Bytes::from_native_slice(&u32::to_be_bytes(self))
    }

    #[cfg(not(feature = "release"))]
    fn into_bytes(self) -> Bytes {
        Bytes::from_seq(&U32_to_be_bytes(U32(self)))
    }
}
#[cfg(not(feature = "release"))]
impl U32Trait for U32 {
    fn into_bytes(self) -> Bytes {
        Bytes::from_seq(&U32_to_be_bytes(self))
    }
}

#[cfg(feature = "release")]
#[inline(always)]
pub fn DoubleByte(x: u16) -> DoubleByte {
    x
}

#[cfg(not(feature = "release"))]
#[inline(always)]
pub fn DoubleByte(x: u16) -> DoubleByte {
    U16(x)
}

#[cfg(feature = "release")]
#[inline(always)]
pub fn QuadByte(x: u32) -> QuadByte {
    x
}

#[cfg(not(feature = "release"))]
#[inline(always)]
pub fn QuadByte(x: u32) -> QuadByte {
    U32(x)
}
