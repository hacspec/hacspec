///! 
///! A set of mathematical utility functions.
///! TODO: T might be a signed integer! Everything in here only considers unsigned really.
///! 

use crate::prelude::*;

// FIXME: Add wrapping ops to Numeric
pub trait TempNumeric : Numeric {
    const NUM_BITS: usize;
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    fn wrap_sub(self, y: Self) -> Self;
    fn wrap_add(self, y: Self) -> Self;
    fn get_bit(self, i: usize) -> Self;
    fn set_bit(self, b: Self, i: usize) -> Self;
    fn set(self, pos: usize, val: Self, i: usize) -> Self;
}

macro_rules! implement_temp_numeric {
    ($t:ty, $bits:literal) => {
        impl TempNumeric for $t {
            const NUM_BITS: usize = $bits;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const TWO: Self = 2;

            #[inline]
            fn wrap_sub(self, y: Self) -> Self {
                self.wrapping_sub(y)
            }

            #[inline]
            fn wrap_add(self, y: Self) -> Self {
                self.wrapping_add(y)
            }

            #[inline]
            fn get_bit(self, i: usize) -> Self {
                (self >> i) & 1
            }
            
            #[inline]
            fn set_bit(self, b: Self, i: usize) -> Self {
                debug_assert!(b == 1 || b == 0);
                let tmp1 = !(1 << i);
                let tmp2 = b << i;
                (self & tmp1) | tmp2
            }
            
            #[inline]
            fn set(self, pos: usize, y: Self, yi: usize) -> Self {
                let b = y.get_bit(yi);
                self.set_bit(b, pos)
            }
        }
    };
}

implement_temp_numeric!(u8, 8);
implement_temp_numeric!(u16, 16);
implement_temp_numeric!(u32, 32);
implement_temp_numeric!(u64, 64);
implement_temp_numeric!(u128, 128);

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
pub fn cset_bit<T: TempNumeric>(x: T, b: T, i: usize, c: T) -> T {
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

