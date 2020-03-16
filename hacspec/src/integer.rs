//!
//! Machine Integer trait and implementations for built-in machine integers
//! and secret integers.
//! 

use crate::prelude::*;

/// Trait that needs to be implemented by all integers that are used as coefficients.
/// This is done here for ℤn over `i128` and `u128`.
pub trait Integer<T> {
    fn from_literal(x: u128) -> T;
    fn from_signed_literal(x: i128) -> T;
    fn inv(x: T, n: T) -> T;
    // fn max() -> T;
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

    // The following functions implement non-constant time operations
    // TODO: This is currently declassifying secret integers!

    /// Equality
    fn equal(self, other: T) -> bool;
    /// Greater than
    fn greater_than(self, other: T) -> bool;
    /// Greater than or equal
    fn greater_than_or_qual(self, other: T) -> bool;
    /// Less than
    fn less_than(self, other: T) -> bool;
    /// Less than or equal
    fn less_than_or_equal(self, other: T) -> bool;
    /// Division `self / other`
    fn div(self, other: T) -> T;
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
            fn inv(x: $t, n: $t) -> $t {
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
            // #[inline]
            // fn max() -> $t {
            //     <$t>::max_value()
            // }
            #[inline]
            fn abs(self) -> $t {
                self
            }

            /// Equality
            fn equal(self, other: $t) -> bool {
                self == other
            }
            /// Greater than
            fn greater_than(self, other: $t) -> bool {
                self > other
            }
            /// Greater than or equal
            fn greater_than_or_qual(self, other: $t) -> bool {
                self >= other
            }
            /// Less than
            fn less_than(self, other: $t) -> bool {
                self < other
            }
            /// Less than or equal
            fn less_than_or_equal(self, other: $t) -> bool {
                self <= other
            }
            /// Division `self / other`
            fn div(self, other: $t) -> $t {
                self / other
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
    fn inv(x: i128, n: i128) -> i128 {
        extended_euclid_invert(x.abs(), n.abs(), true)
    }
    #[inline]
    fn sub_lift(self, rhs: i128, n: i128) -> i128 {
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
    // #[inline]
    // fn max() -> i128 {
    //     i128::max_value()
    // }
    #[inline]
    fn abs(self) -> i128 {
        self.abs()
    }
    /// Equality
    fn equal(self, other: i128) -> bool {
        self == other
    }
    /// Greater than
    fn greater_than(self, other: i128) -> bool {
        self > other
    }
    /// Greater than or equal
    fn greater_than_or_qual(self, other: i128) -> bool {
        self >= other
    }
    /// Less than
    fn less_than(self, other: i128) -> bool {
        self < other
    }
    /// Less than or equal
    fn less_than_or_equal(self, other: i128) -> bool {
        self <= other
    }
    /// Division `self / other`
    fn div(self, other: i128) -> i128 {
        self / other
    }
}

#[macro_export]
macro_rules! impl_unsigned_secret_integer {
    ($t:ty,$base:ty) => {
        impl Integer<$t> for $t {
            /// Cast to this type can be unsafe.
            #[inline]
            fn from_literal(x: u128) -> $t {
                <$t>::classify(x as $base)
            }
            #[inline]
            fn from_signed_literal(x: i128) -> $t {
                <$t>::classify(x as $base)
            }
            /// **Panics**
            #[inline]
            fn inv(x: $t, n: $t) -> $t {
                let x: u128 = <$t>::declassify(x) as u128;
                let n: u128 = <$t>::declassify(n) as u128;
                <$t>::classify(extended_euclid_invert(x, n, false) as $base)
            }
            #[inline]
            fn sub_lift(self, rhs: $t, n: $t) -> $t {
                self.sub_mod(rhs, n)
            }
            #[inline]
            fn sub_mod(self, rhs: $t, n: $t) -> $t {
                let rhs: u128 = <$t>::declassify(rhs) as u128;
                let n: u128 = <$t>::declassify(n) as u128;
                let s: u128 = <$t>::declassify(self) as u128;
                if n == 0 {
                    return <$t>::classify((s - rhs) as $base);
                }
        
                let mut lhs = s;
                while lhs < rhs {
                    lhs += n;
                }
                <$t>::classify((lhs - rhs) as $base)
            }
            #[inline]
            fn add_mod(self, rhs: $t, n: $t) -> $t {
                let rhs: u128 = <$t>::declassify(rhs) as u128;
                let n: u128 = <$t>::declassify(n) as u128;
                let s: u128 = <$t>::declassify(self) as u128;
                if n != 0 {
                    <$t>::classify(((s + rhs) % n) as $base)
                } else {
                    <$t>::classify((s + rhs) as $base)
                }
            }
            #[inline]
            fn mul_mod(self, rhs: $t, n: $t) -> $t {
                let rhs: u128 = <$t>::declassify(rhs) as u128;
                let n: u128 = <$t>::declassify(n) as u128;
                let s: u128 = <$t>::declassify(self) as u128;
                if n == 0 {
                    <$t>::classify((s * rhs) as $base)
                } else {
                    <$t>::classify(((s * rhs) % n) as $base)
                }
            }
            #[inline]
            fn rem(self, n: $t) -> $t {
                let n: u128 = <$t>::declassify(n) as u128;
                let s: u128 = <$t>::declassify(self) as u128;
                <$t>::classify((s % n) as $base)
            }
            // #[inline]
            // fn max() -> $t {
            //     <$t>::max_value()
            // }
            #[inline]
            fn abs(self) -> $t {
                self
            }

            /// Equality
            /// NOTE: This is not constant time!
            fn equal(self, other: $t) -> bool {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                s == o
            }
            /// Greater than
            /// NOTE: This is not constant time!
            fn greater_than(self, other: $t) -> bool {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                s > o
            }
            /// Greater than or equal
            /// NOTE: This is not constant time!
            fn greater_than_or_qual(self, other: $t) -> bool {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                s >= o
            }
            /// Less than
            /// NOTE: This is not constant time!
            fn less_than(self, other: $t) -> bool {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                s < o
            }
            /// Less than or equal
            /// NOTE: This is not constant time!
            fn less_than_or_equal(self, other: $t) -> bool {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                s <= o
            }
            /// Division `self / other`
            /// NOTE: This is not constant time!
            fn div(self, other: $t) -> $t {
                let s: u128 = <$t>::declassify(self) as u128;
                let o: u128 = <$t>::declassify(other) as u128;
                <$t>::classify((s / o) as u128)
            }
        }
    };
}

// impl_unsigned_secret_integer!(U8, u8);
// impl_unsigned_secret_integer!(U16, u16);
// impl_unsigned_secret_integer!(U32, u32);
// impl_unsigned_secret_integer!(U64, u64);
impl_unsigned_secret_integer!(U128, u128);

/// Traits that have to be implemented by the type used for coefficients.
pub trait TRestrictions<T>:
    Default
    + Integer<T>
    + Copy
    + Clone
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
        + Add<T, Output = T>
        + Sub<T, Output = T>
        + Mul<T, Output = T>
        + Debug
{
}
