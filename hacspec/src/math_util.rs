///! 
///! A set of mathematical utility functions.
///! TODO: T might be a signed integer! Everything in here only considers unsigned really.
///! 

use crate::prelude::*;

/// Rust's built-in modulo (x % n) is signed. This lifts x into ℤn+.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub(crate) fn signed_mod(x: i128, n: i128) -> i128 {
    let mut ret = x % n;
    while ret < 0 {
        ret += n;
    }
    ret
}

/// Extended euclidean algorithm to compute the inverse of x in ℤ/n
///
/// **Panics** if x is not invertible.
///
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub(crate) fn extended_euclid_invert<T: Integer>(x: T, n: T, signed: bool) -> T {
    let mut t = T::ZERO;
    let mut r = n;
    let mut new_t = T::ONE;
    let mut new_r = x;

    println!("n: {:?}", n);
    while !new_r.equal(T::ZERO) {
        let q: T = r.div(new_r);

        let tmp = new_r.clone();
        // XXX: a little hacky
        let tmp_prod = q * new_r;
        let mut tmp_r = r;
        while tmp_r.less_than(tmp_prod) {
            tmp_r = tmp_r + n;
        }
        new_r = tmp_r - tmp_prod;
        r = tmp;

        let tmp = new_t.clone();
        // XXX: a little hacky
        let tmp_prod = q * new_t;
        let mut tmp_t = t;
        while tmp_t.less_than(tmp_prod) {
            tmp_t = tmp_t + n;
        }
        new_t = tmp_t - tmp_prod;
        t = tmp;
    }

    if r.greater_than(T::ONE) && !x.equal(T::ZERO) {
        panic!("{:x?} is not invertible in ℤ/{:x?}", x, n);
    }
    if t.less_than(T::ZERO) {
        if signed {
            t = t.abs()
        } else {
            t = t + n
        };
    };

    t
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == 1`.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cswap_bit<T: Integer>(x: T, y: T, c: T) -> (T, T) {
    cswap(x, y, T::default().wrap_sub(c))
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == T::max`.
/// The return value is undefined if `c` has any other value.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cswap<T: Integer>(x: T, y: T, c: T) -> (T, T) {
    let mask = c & (x ^ y);
    (x ^ mask, y ^ mask)
}

/// Set bit at position `i` in `x` to `b` if `c` is all 1 and return the restult.
/// Returns `x` if `c` is `0`.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cset_bit<T: Integer>(x: T, b: T, i: u32, c: T) -> T {
    let set = x.set_bit(b, i);
    let (out, _) = cswap(x, set, c);
    out
}

/// Add two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cadd<T: Integer>(x: T, y: T, c: T) -> T {
    let sum = x.wrap_add(y);
    let (x, _) = cswap(x, sum, c);
    x
}

/// Subtract two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn csub<T: Integer>(x: T, y: T, c: T) -> T {
    let diff = x.wrap_sub(y);
    let (x, _) = cswap(x, diff, c);
    x
}

/// Multiply two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Multiplication is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cmul<T: Integer>(x: T, y: T, c: T) -> T {
    let prod = x.wrap_mul(y);
    let (x, _) = cswap(x, prod, c);
    x
}

/// Constant time division for Numerics.
/// Note that this function is only constant time if `T` is a secret integer and
/// hence provides constant time implementations for the used functions.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn ct_div<T: Integer>(a: T, d: T) -> (T, T) {
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
