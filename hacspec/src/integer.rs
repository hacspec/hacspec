use std::fmt::Debug;
use std::ops::{Add, Div, Mul, Sub};

use crate::poly::*;

/// Trait that needs to be implemented by all integers that are used as coefficients.
/// This is done here for ℤn over `i128` and `u128`.
pub trait Integer<T> {
    fn from_literal(x: u128) -> T;
    fn from_signed_literal(x: i128) -> T;
    fn invert(x: T, n: T) -> T;
    fn max() -> T;
    /// Lift the possibly negative result back up mod n.
    fn sub_lift(self, rhs: T, n: T) -> T;
    /// Compute (self - rhs) % n.
    fn sub_mod(self, rhs: T, n: T) -> T;
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: T, n: T) -> T;
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: T, n: T) -> T;
    /// `self % n`
    fn rem(self, n: T) -> T;
    fn abs(self) -> T;
}

#[macro_export]
macro_rules! impl_unsigned_integer {
    ($t:ty) => {
        impl Integer<$t> for $t {
            /// Cast to this type can be unsafe.
            #[inline]
            fn from_literal(x: u128) -> $t {
                x as $t
            }
            #[inline]
            fn from_signed_literal(x: i128) -> $t {
                x as $t
            }
            /// **Panics**
            #[inline]
            fn invert(x: $t, n: $t) -> $t {
                extended_euclid_invert(x, n, false)
            }
            #[inline]
            fn sub_lift(self, rhs: $t, n: $t) -> $t {
                self.sub_mod(rhs, n)
            }
            #[inline]
            fn sub_mod(self, rhs: $t, n: $t) -> $t {
                if n == 0 {
                    return self - rhs;
                }

                let mut lhs = self;
                while lhs < rhs {
                    lhs += n;
                }
                lhs - rhs
            }
            #[inline]
            fn add_mod(self, rhs: $t, n: $t) -> $t {
                if n != 0 {
                    (self + rhs) % n
                } else {
                    self + rhs
                }
            }
            #[inline]
            fn mul_mod(self, rhs: $t, n: $t) -> $t {
                if n == 0 {
                    self * rhs
                } else {
                    (self * rhs) % n
                }
            }
            #[inline]
            fn rem(self, n: $t) -> $t {
                self % n
            }
            #[inline]
            fn max() -> $t {
                <$t>::max_value()
            }
            #[inline]
            fn abs(self) -> $t {
                self
            }
        }
    };
}

impl_unsigned_integer!(usize);
impl_unsigned_integer!(u8);
impl_unsigned_integer!(u16);
impl_unsigned_integer!(u32);
impl_unsigned_integer!(u64);
impl_unsigned_integer!(u128);

impl Integer<i128> for i128 {
    /// **Warning** might be lossy
    #[inline]
    fn from_literal(x: u128) -> i128 {
        x as i128
    }
    #[inline]
    fn from_signed_literal(x: i128) -> i128 {
        x
    }
    #[inline]
    fn invert(x: i128, n: i128) -> i128 {
        extended_euclid_invert(x.abs(), n.abs(), true)
    }
    #[inline]
    fn sub_lift(self, rhs: i128, _n: i128) -> i128 {
        self - rhs
    }
    #[inline]
    fn sub_mod(self, rhs: i128, n: i128) -> i128 {
        if n != 0 {
            signed_mod(self - rhs, n)
        } else {
            self - rhs
        }
    }
    #[inline]
    fn add_mod(self, rhs: i128, n: i128) -> i128 {
        if n != 0 {
            signed_mod(self + rhs, n)
        } else {
            self + rhs
        }
    }
    #[inline]
    fn mul_mod(self, rhs: i128, n: i128) -> i128 {
        if n == 0 {
            self * rhs
        } else {
            (self * rhs) % n
        }
    }
    #[inline]
    fn rem(self, n: i128) -> i128 {
        self % n
    }
    #[inline]
    fn max() -> i128 {
        i128::max_value()
    }
    #[inline]
    fn abs(self) -> i128 {
        self.abs()
    }
}

/// Traits that have to be implemented by the type used for coefficients.
pub trait TRestrictions<T>:
    Default
    + Integer<T>
    + Copy
    + Clone
    + PartialEq
    + PartialOrd
    + Div<T, Output = T>
    + Add<T, Output = T>
    + Sub<T, Output = T>
    + Mul<T, Output = T>
    + Debug
{
}
impl<T> TRestrictions<T> for T where
    T: Default
        + Integer<T>
        + Copy
        + Clone
        + PartialEq
        + PartialOrd
        + Div<T, Output = T>
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + Mul<T, Output = T>
        + Debug
{
}
