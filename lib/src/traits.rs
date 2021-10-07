//!
//! This module specifies the `Numeric` trait.
//!

use crate::prelude::*;

/// Common trait for all byte arrays and sequences.
pub trait SeqTrait<T: Clone>:
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
    /// use hacspec_lib::prelude::*;
    ///
    /// let mut s = Seq::<u8>::new(5);
    /// let tmp = Seq::<u8>::from_native_slice(&[2, 3]);
    /// s = s.update_slice(2, &tmp, 1, 1);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 3, 0, 0]));
    /// ```
    fn update_slice<A: SeqTrait<T>>(
        self,
        start_out: usize,
        v: &A,
        start_in: usize,
        len: usize,
    ) -> Self;

    /// Update this sequence with `v` starting at `start`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hacspec_lib::prelude::*;
    ///
    /// let mut s = Seq::<u8>::new(5);
    /// let tmp = Seq::<u8>::from_native_slice(&[2, 3]);
    /// s = s.update(2, &tmp);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 2, 3, 0]));
    /// ```
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn update<A: SeqTrait<T>>(self, start: usize, v: &A) -> Self {
        let len = v.len();
        self.update_slice(start, v, 0, len)
    }

    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn update_start<A: SeqTrait<T>>(self, v: &A) -> Self {
        let len = v.len();
        self.update_slice(0, v, 0, len)
    }
}

/// This trait extends the `Numeric` trait and is implemented by all integer
/// types. It offers bit manipulation, instantiation from literal, and convenient
/// constants.
pub trait Integer: Numeric {
    const NUM_BITS: usize;

    // Some useful values.
    // Not constants because math integers can't do that.
    #[allow(non_snake_case)]
    fn ZERO() -> Self;
    #[allow(non_snake_case)]
    fn ONE() -> Self;
    #[allow(non_snake_case)]
    fn TWO() -> Self;

    /// Get an integer with value `val`.
    fn from_literal(val: u128) -> Self;

    /// Read a hex string (starting with 0x) into an `Integer`.
    fn from_hex_string(s: &String) -> Self;

    fn get_bit(self, i: usize) -> Self;

    fn set_bit(self, b: Self, i: usize) -> Self;

    fn set(self, pos: usize, y: Self, yi: usize) -> Self;

    fn rotate_left(self, n: usize) -> Self;

    fn rotate_right(self, n: usize) -> Self;
}

pub trait SecretInteger: Integer {
    type PublicVersion: PublicInteger;
    fn classify(x: Self::PublicVersion) -> Self;
}
pub trait SecretIntegerCopy: SecretInteger + Copy {
    type PublicVersionCopy: PublicIntegerCopy;
    fn classify(x: Self::PublicVersionCopy) -> Self;
}

pub trait PublicInteger: Integer {
    type SecretVersion: Integer;
}
pub trait PublicIntegerCopy: PublicInteger + Copy {
    type SecretVersionCopy: Integer + Copy;
}

pub trait UnsignedInteger: Integer {}
pub trait UnsignedIntegerCopy: UnsignedInteger + Copy {}

pub trait SignedInteger: Integer {}
pub trait SignedIntegerCopy: SignedInteger + Copy {}

pub trait UnsignedSecretInteger: UnsignedInteger + SecretInteger {
    fn to_le_bytes(self) -> Seq<U8>;
    fn to_be_bytes(self) -> Seq<U8>;
    fn from_le_bytes(x: &Seq<U8>) -> Self;
    fn from_be_bytes(x: &Seq<U8>) -> Self;
    /// Get byte `i` of this integer.
    #[inline]
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn get_byte(self, i: usize) -> Self {
        (self >> (i * 8)) & ((Self::ONE() << 8) - Self::ONE())
    }
}
pub trait UnsignedSecretIntegerCopy: UnsignedSecretInteger + SecretIntegerCopy {}

pub trait UnsignedPublicInteger: UnsignedInteger + PublicInteger {
    fn to_le_bytes(self) -> Seq<u8>;
    fn to_be_bytes(self) -> Seq<u8>;
    fn from_le_bytes(x: &Seq<u8>) -> Self;
    fn from_be_bytes(x: &Seq<u8>) -> Self;
}
pub trait UnsignedPublicIntegerCopy: UnsignedPublicInteger + PublicIntegerCopy {}

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
    /// `self % n` that always returns a positive integer
    fn signed_modulo(self, n: Self) -> Self;
    /// `|self|`
    fn absolute(self) -> Self;
}

pub trait NumericCopy: Copy {}

/// The `Numeric` trait has to be implemented by all numeric objects.
pub trait Numeric:
    ModNumeric
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + BitXor<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitAnd<Self, Output = Self>
    + Shl<usize, Output = Self>
    + Shr<usize, Output = Self>
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
    fn exp(self, exp: u32) -> Self;
    /// `self ^ exp` where `exp` is a `Self`.
    fn pow_self(self, exp: Self) -> Self;
    /// Division.
    fn divide(self, rhs: Self) -> Self;
    /// Invert self modulo n.
    fn inv(self, n: Self) -> Self;

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
    fn greater_than_or_equal_bm(self, other: Self) -> Self;
    fn less_than_bm(self, other: Self) -> Self;
    fn less_than_or_equal_bm(self, other: Self) -> Self;
}
