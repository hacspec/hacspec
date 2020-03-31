///! 
///! A set of mathematical utility functions.
/// 

use crate::prelude::*;

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == 1`.
#[inline]
pub fn cswap_bit<T: Numeric>(x: T, y: T, c: T) -> (T, T) {
    cswap(x, y, T::default().wrap_sub(c))
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == T::max`.
/// The return value is undefined if `c` has any other value.
#[inline]
pub fn cswap<T: Numeric>(x: T, y: T, c: T) -> (T, T) {
    // TODO: T might be a signed integer!
    let mask = c & (x ^ y);
    (x ^ mask, y ^ mask)
}
