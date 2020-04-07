//!
//! This module specifies the `Numeric` trait.
//!

use crate::prelude::*;

/// Common trait for all byte arrays and sequences.
pub trait SeqTrait<T: Copy> : Index<usize, Output=T> + IndexMut<usize, Output=T> + Sized {
    fn len(&self) -> usize;
    fn iter(&self) -> std::slice::Iter<T>;
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
    /// s = s.update_sub(2, tmp, 1, 1);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 3, 0, 0]));
    /// ```
    fn update_sub<A: SeqTrait<T>>(
        mut self,
        start_out: usize,
        v: A,
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
    /// s = s.update(2, tmp);
    /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 2, 3, 0]));
    /// ```
    #[library(hacspec)]
    fn update<A: SeqTrait<T>>(self, start: usize, v: A) -> Self {
        let len = v.len();
        self.update_sub(start, v, 0, len)
    }

    #[library(hacspec)]
    fn update_start<A: SeqTrait<T>>(
        self,
        v: A
    ) -> Self {
        let len = v.len();
        self.update_sub(0, v, 0, len)
    }
}

pub trait SecretInteger {}

impl SecretInteger for U8 {}
impl SecretInteger for U16 {}
impl SecretInteger for U32 {}
impl SecretInteger for U128 {}
impl SecretInteger for I8 {}
impl SecretInteger for I16 {}
impl SecretInteger for I32 {}
impl SecretInteger for I128 {}

pub trait PublicInteger {}

impl PublicInteger for u8 {}
impl PublicInteger for u16 {}
impl PublicInteger for u32 {}
impl PublicInteger for u128 {}
impl PublicInteger for i8 {}
impl PublicInteger for i16 {}
impl PublicInteger for i32 {}
impl PublicInteger for i128 {}

pub trait Numeric: NumericBase + Copy {}

/// The `Numeric` trait has to be implemented by all numeric objects.
pub trait NumericBase:
    Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + BitXor<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitAnd<Self, Output = Self>
    + Shl<u32, Output = Self>
    + Shr<u32, Output = Self>
    + Not
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
    /// (self - rhs) % n.
    fn sub_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: Self, n: Self) -> Self;
    /// `(self ^ exp) % n`
    fn pow_mod(self, exp: Self, n: Self) -> Self;
    /// Division.
    fn div(self, rhs: Self) -> Self;
    /// `self % n`
    fn rem(self, n: Self) -> Self;
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
