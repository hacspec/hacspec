//!
//! This module specifies the `Numeric` trait.
//!

use crate::prelude::*;

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
