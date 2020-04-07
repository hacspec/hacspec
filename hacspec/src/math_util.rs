///! 
///! A set of mathematical utility functions.
///! TODO: T might be a signed integer! Everything in here only considers unsigned really.
///! 

use crate::prelude::*;

// FIXME: Add wrapping ops to Numeric
pub trait TempNumeric : Numeric {
    const NUM_BITS: u32;
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    fn from_literal(val: u128) -> Self;
    fn wrap_sub(self, y: Self) -> Self;
    fn wrap_add(self, y: Self) -> Self;
    fn wrap_mul(self, y: Self) -> Self;
    #[inline]
    fn get_bit(self, i: u32) -> Self {
        (self >> i) & Self::ONE
    }
    #[inline]
    fn set_bit(self, b: Self, i: u32) -> Self {
        debug_assert!(b.equal(Self::ONE) || b.equal(Self::ZERO));
        let tmp1 = Self::from_literal(!(1 << i));
        let tmp2 = b << i;
        (self & tmp1) | tmp2
    }
    #[inline]
    fn set(self, pos: u32, y: Self, yi: u32) -> Self {
        let b = y.get_bit(yi);
        self.set_bit(b, pos)
    }
}

macro_rules! implement_temp_numeric {
    ($t:ty, $bits:literal) => {
        impl TempNumeric for $t {
            const NUM_BITS: u32 = $bits;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const TWO: Self = 2;

            #[inline]
            fn from_literal(val: u128) -> Self {
                val as $t
            }

            #[inline]
            fn wrap_sub(self, y: Self) -> Self {
                self.wrapping_sub(y)
            }

            #[inline]
            fn wrap_add(self, y: Self) -> Self {
                self.wrapping_add(y)
            }

            #[inline]
            fn wrap_mul(self, y: Self) -> Self {
                self.wrapping_mul(y)
            }
        }
    };
}

macro_rules! implement_temp_secret_numeric {
    ($t:ident, $base:ty, $bits:literal) => {
        impl TempNumeric for $t {
            const NUM_BITS: u32 = $bits;
            const ZERO: Self = $t(0);
            const ONE: Self = $t(1);
            const TWO: Self = $t(2);

            #[inline]
            fn from_literal(val: u128) -> Self {
                Self::classify(val as $base)
            }

            #[inline]
            fn wrap_sub(self, y: Self) -> Self {
                self - y
            }

            #[inline]
            fn wrap_add(self, y: Self) -> Self {
                self + y
            }

            #[inline]
            fn wrap_mul(self, y: Self) -> Self {
                self * y
            }
        }
    };
}

implement_temp_numeric!(u8, 8);
implement_temp_numeric!(u16, 16);
implement_temp_numeric!(u32, 32);
implement_temp_numeric!(u64, 64);
implement_temp_numeric!(u128, 128);

implement_temp_secret_numeric!(U8, u8, 8);
implement_temp_secret_numeric!(U16, u16, 16);
implement_temp_secret_numeric!(U32, u32, 32);
implement_temp_secret_numeric!(U64, u64, 64);
implement_temp_secret_numeric!(U128, u128, 128);

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == 1`.
#[inline]
pub fn cswap_bit<T: TempNumeric>(x: T, y: T, c: T) -> (T, T) {
    cswap(x, y, T::default().wrap_sub(c))
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == T::max`.
/// The return value is undefined if `c` has any other value.
#[inline]
pub fn cswap<T: TempNumeric>(x: T, y: T, c: T) -> (T, T) {
    let mask = c & (x ^ y);
    (x ^ mask, y ^ mask)
}

/// Set bit at position `i` in `x` to `b` if `c` is all 1 and return the restult.
/// Returns `x` if `c` is `0`.
#[inline]
pub fn cset_bit<T: TempNumeric>(x: T, b: T, i: u32, c: T) -> T {
    let set = x.set_bit(b, i);
    let (out, _) = cswap(x, set, c);
    out
}

/// Add two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
pub fn cadd<T: TempNumeric>(x: T, y: T, c: T) -> T {
    let sum = x.wrap_add(y);
    let (x, _) = cswap(x, sum, c);
    x
}

/// Subtract two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
pub fn csub<T: TempNumeric>(x: T, y: T, c: T) -> T {
    let diff = x.wrap_sub(y);
    let (x, _) = cswap(x, diff, c);
    x
}

/// Multiply two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Multiplication is always wrapping.
#[inline]
pub fn cmul<T: TempNumeric>(x: T, y: T, c: T) -> T {
    let prod = x.wrap_mul(y);
    let (x, _) = cswap(x, prod, c);
    x
}

/// Constant time division for Numerics.
/// Note that this function is only constant time if `T` is a secret integer and
/// hence provides constant time implementations for the used functions.
#[inline]
pub fn ct_div<T: TempNumeric>(a: T, d: T) -> (T, T) {
    let mut q = T::default();
    let mut r = T::default();
    for i in (0..T::NUM_BITS).rev() {
        r = r << 1;
        r = r.set(0, a, i);
        // The code below is equivalent to the following.
        // if r.greater_than_or_qual(d) {
        //     r = r - d;
        //     q = q.set_bit(T::ONE, i);
        // }
        let geq = r.greater_than_or_qual_bm(d);
        r = csub(r, d, geq);
        q = cset_bit(q, T::ONE, i, geq);
    }
    (q, r)
}
