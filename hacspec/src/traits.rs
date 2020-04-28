//!
//! This module specifies the `Numeric` trait.
//!

use crate::prelude::*;

/// Common trait for all byte arrays and sequences.
pub trait SeqTrait<T: Copy>:
    Index<usize, Output = T> + IndexMut<usize, Output = T> + Sized
{
    fn len(&self) -> usize;
    fn iter(&self) -> std::slice::Iter<T>;
    fn create(len: usize) -> Self;
    /// Update this sequence with `l` elements of `v`, starting at `start_in`,
    /// at `start_out`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hacspec::prelude::*;
    ///
    /// let mut s = Seq::<u8>::new(5);
    /// let tmp = Seq::<u8>::from_slice(&[2, 3]);
    /// s = s.update_sub(2, &tmp, 1, 1);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 3, 0, 0]));
    /// ```
    fn update_sub<A: SeqTrait<T>>(
        mut self,
        start_out: usize,
        v: &A,
        start_in: usize,
        len: usize,
    ) -> Self {
        debug_assert!(self.len() >= start_out + len);
        debug_assert!(v.len() >= start_in + len);
        for i in 0..len {
            self[start_out + i] = v[start_in + i];
        }
        self
    }

    /// Update this sequence with `v` starting at `start`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hacspec::prelude::*;
    ///
    /// let mut s = Seq::<u8>::new(5);
    /// let tmp = Seq::<u8>::from_slice(&[2, 3]);
    /// s = s.update(2, &tmp);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 2, 3, 0]));
    /// ```
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn update<A: SeqTrait<T>>(self, start: usize, v: &A) -> Self {
        let len = v.len();
        self.update_sub(start, v, 0, len)
    }

    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn update_start<A: SeqTrait<T>>(self, v: &A) -> Self {
        let len = v.len();
        self.update_sub(0, v, 0, len)
    }
}

// FIXME: rename
/// This trait extends the `Numeric` trait and is implemented by all integer
/// types. It offers bit manipulation, instantiation from literal, and convenient
/// constants.
pub trait Integer: Numeric {
    const NUM_BITS: u32;
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;

    /// Get an integer with value `val`.
    fn from_literal(val: u128) -> Self;

    /// Get bit `i` of this integer.
    #[inline]
    fn get_bit(self, i: u32) -> Self {
        (self >> i) & Self::ONE
    }

    /// Set bit `i` of this integer to `b` and return the result.
    /// Bit `b` has to be `0` or `1`.
    #[inline]
    fn set_bit(self, b: Self, i: u32) -> Self {
        debug_assert!(b.equal(Self::ONE) || b.equal(Self::ZERO));
        let tmp1 = Self::from_literal(!(1 << i));
        let tmp2 = b << i;
        (self & tmp1) | tmp2
    }

    /// Set bit `pos` of this integer to bit `yi` of integer `y`.
    #[inline]
    fn set(self, pos: u32, y: Self, yi: u32) -> Self {
        let b = y.get_bit(yi);
        self.set_bit(b, pos)
    }

    fn rotate_left(self, n: u32) -> Self {
        // Taken from https://blog.regehr.org/archives/1063
        assert!(n < Self::NUM_BITS);
        (self << n) | (self >> ((-(n as i32) as u32) & (Self::NUM_BITS - 1)))
    }

    fn rotate_right(self, n: u32) -> Self {
        // Taken from https://blog.regehr.org/archives/1063
        assert!(n < Self::NUM_BITS);
        (self >> n) | (self << ((-(n as i32) as u32) & (Self::NUM_BITS - 1)))
    }
}

pub trait SecretInteger: Integer {
    type PublicVersion : Integer;
    fn classify(x: Self::PublicVersion) -> Self;
}

impl SecretInteger for U8 {
    type PublicVersion = u8;
    fn classify(x: Self::PublicVersion) -> Self {
        U8(x)
    }
}
impl SecretInteger for U16 {
    type PublicVersion = u16;
    fn classify(x: Self::PublicVersion) -> Self {
        U16(x)
    }
}
impl SecretInteger for U32 {
    type PublicVersion = u32;
    fn classify(x: Self::PublicVersion) -> Self {
        U32(x)
    }
}
impl SecretInteger for U64 {
    type PublicVersion = u64;
    fn classify(x: Self::PublicVersion) -> Self {
        U64(x)
    }
}
impl SecretInteger for U128 {
    type PublicVersion = u128;
    fn classify(x: Self::PublicVersion) -> Self {
        U128(x)
    }
}
impl SecretInteger for I8 {
    type PublicVersion = i8;
    fn classify(x: Self::PublicVersion) -> Self {
        I8(x)
    }
}
impl SecretInteger for I16 {
    type PublicVersion = i16;
    fn classify(x: Self::PublicVersion) -> Self {
        I16(x)
    }
}
impl SecretInteger for I32 {
    type PublicVersion = i32;
    fn classify(x: Self::PublicVersion) -> Self {
        I32(x)
    }
}
impl SecretInteger for I64 {
    type PublicVersion = i64;
    fn classify(x: Self::PublicVersion) -> Self {
        I64(x)
    }
}
impl SecretInteger for I128 {
    type PublicVersion = i128;
    fn classify(x: Self::PublicVersion) -> Self {
        I128(x)
    }
}

pub trait PublicInteger: Integer {
    type SecretVersion : Integer;
}

impl PublicInteger for u8 {
    type SecretVersion = U8;
}
impl PublicInteger for u16 {
    type SecretVersion = U16;
}
impl PublicInteger for u32 {
    type SecretVersion = U32;
}
impl PublicInteger for u64 {
    type SecretVersion = U64;
}
impl PublicInteger for u128 {
    type SecretVersion = U128;
}
impl PublicInteger for i8 {
    type SecretVersion = I8;
}
impl PublicInteger for i16 {
    type SecretVersion = I16;
}
impl PublicInteger for i32 {
    type SecretVersion = I32;
}
impl PublicInteger for i64 {
    type SecretVersion = I64;
}
impl PublicInteger for i128 {
    type SecretVersion = I128;
}

pub trait UnsignedInteger: Integer {}

impl UnsignedInteger for U8 {}
impl UnsignedInteger for U16 {}
impl UnsignedInteger for U32 {}
impl UnsignedInteger for U64 {}
impl UnsignedInteger for U128 {}
impl UnsignedInteger for u8 {}
impl UnsignedInteger for u16 {}
impl UnsignedInteger for u32 {}
impl UnsignedInteger for u64 {}
impl UnsignedInteger for u128 {}

pub trait SignedInteger: Integer {}

impl SignedInteger for I8 {}
impl SignedInteger for I16 {}
impl SignedInteger for I32 {}
impl SignedInteger for I64 {}
impl SignedInteger for I128 {}
impl SignedInteger for i8 {}
impl SignedInteger for i16 {}
impl SignedInteger for i32 {}
impl SignedInteger for i64 {}
impl SignedInteger for i128 {}

pub trait UnsignedSecretInteger : UnsignedInteger + SecretInteger {
    fn to_le_bytes(self) -> Seq<U8>;
    fn to_be_bytes(self) -> Seq<U8>;
    fn from_le_bytes(x: &Seq<U8>) -> Self;
    fn from_be_bytes(x: &Seq<U8>) -> Self;
}

impl UnsignedSecretInteger for U8 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<U8>{
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<U8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
}

impl UnsignedSecretInteger for U16 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U16_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U16_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U16_from_le_bytes(U16Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U16_from_be_bytes(U16Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U32 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U32_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U32_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U32_from_le_bytes(U32Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U32_from_be_bytes(U32Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U64 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U64_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U64_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U64_from_le_bytes(U64Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U64_from_be_bytes(U64Word::from_seq(x))
    }
}

impl UnsignedSecretInteger for U128 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U128_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<U8> {
        Seq::from_seq(&U128_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<U8>) -> Self {
        U128_from_le_bytes(U128Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<U8>) -> Self {
        U128_from_be_bytes(U128Word::from_seq(x))
    }
}

pub trait UnsignedPublicInteger : UnsignedInteger + PublicInteger {
    fn to_le_bytes(self) -> Seq<u8>;
    fn to_be_bytes(self) -> Seq<u8>;
    fn from_le_bytes(x: &Seq<u8>) -> Self;
    fn from_be_bytes(x: &Seq<u8>) -> Self;
}

impl UnsignedPublicInteger for u8 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<u8>{
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<u8> {
        let mut x = Seq::new(1);
        x[0] = self;
        x
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        assert!(x.len() == 1);
        x[0]
    }
}

impl UnsignedPublicInteger for u16 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u16_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u16_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u16_from_le_bytes(u16Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u16_from_be_bytes(u16Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u32 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u32_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u32_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u32_from_le_bytes(u32Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u32_from_be_bytes(u32Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u64 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u64_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u64_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u64_from_le_bytes(u64Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u64_from_be_bytes(u64Word::from_seq(x))
    }
}

impl UnsignedPublicInteger for u128 {
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_le_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u128_to_le_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn to_be_bytes(self) -> Seq<u8> {
        Seq::from_seq(&u128_to_be_bytes(self))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_le_bytes(x: &Seq<u8>) -> Self {
        u128_from_le_bytes(u128Word::from_seq(x))
    }
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn from_be_bytes(x: &Seq<u8>) -> Self {
        u128_from_be_bytes(u128Word::from_seq(x))
    }
}

pub trait Numeric: NumericBase + Copy {}

pub trait ModNumeric {
    /// (self - rhs) % n.
    fn sub_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self ^ exp) % n`
    fn pow_mod(self, exp: Self, n: Self) -> Self;
    /// `self % n`
    fn modulo(self, n: Self) -> Self;
}

/// The `Numeric` trait has to be implemented by all numeric objects.
pub trait NumericBase:
    ModNumeric
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + BitXor<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitAnd<Self, Output = Self>
    + Shl<u32, Output = Self>
    + Shr<u32, Output = Self>
    + Not<Output = Self>
    + Default
    + Clone
    + Debug
{
    /// Return largest value that can be represented.
    fn max_val() -> Self;

    fn wrap_add(self, rhs: Self) -> Self;
    fn wrap_sub(self, rhs: Self) -> Self;
    fn wrap_mul(self, rhs: Self) -> Self;
    fn wrap_div(self, rhs: Self) -> Self;

    /// `self ^ exp` where `exp` is a `u32`.
    fn pow(self, exp: u32) -> Self;
    /// `self ^ exp` where `exp` is a `Self`.
    fn pow_self(self, exp: Self) -> Self;
    /// Division.
    fn div(self, rhs: Self) -> Self;
    /// Invert self modulo n.
    fn inv(self, n: Self) -> Self;
    /// `|self|`
    fn abs(self) -> Self;

    // Comparison functions returning bool.
    fn equal(self, other: Self) -> bool;
    fn greater_than(self, other: Self) -> bool;
    fn greater_than_or_qual(self, other: Self) -> bool;
    fn less_than(self, other: Self) -> bool;
    fn less_than_or_equal(self, other: Self) -> bool;

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    fn not_equal_bm(self, other: Self) -> Self;
    fn equal_bm(self, other: Self) -> Self;
    fn greater_than_bm(self, other: Self) -> Self;
    fn greater_than_or_qual_bm(self, other: Self) -> Self;
    fn less_than_bm(self, other: Self) -> Self;
    fn less_than_or_equal_bm(self, other: Self) -> Self;
}
