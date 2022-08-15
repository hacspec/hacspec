#![allow(dead_code)]
///!
///! This module holds utility functions for vector manipulation.
///! This includes sequences, arrays, and polynomials.
///!
use crate::prelude::*;
use alloc::vec::Vec;

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Pad (append) a slice `v` to length `l` with `T::default()`.
pub(crate) fn pad<T: Numeric + Copy>(v: &[T], l: usize) -> Vec<T> {
    let mut out = v.to_vec();
    for _ in out.len()..l {
        out.push(T::default());
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Generate a `Vec<T>` of length `l`, containing the first `l` elements of `v`.
pub(crate) fn make_fixed_length<T: Numeric + Copy>(v: &[T], l: usize) -> Vec<T> {
    let mut out = vec![T::default(); l];
    for (a, &b) in out.iter_mut().zip(v.iter()) {
        *a = b;
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Create a monomial `Vec<T>` with value `c` at position `d`.
pub(crate) fn monomial<T>(c: T, d: usize) -> Vec<T>
where
    T: Numeric + Copy,
{
    let mut p = vec![T::default(); d + 1];
    p[d] = c;
    p
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Return vectors `x` and `y`, padded to maximum length of the two.
pub(crate) fn normalize<T: Numeric + Copy>(x: &[T], y: &[T]) -> (Vec<T>, Vec<T>) {
    let max_len = core::cmp::max(x.len(), y.len());
    (pad(x, max_len), pad(y, max_len))
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Return the leading coefficient (value) of `x` that's non-zero.
/// Returns a (index, coefficient)-Tuple.
pub(crate) fn leading_coefficient<T: Numeric + Copy>(x: &[T]) -> (usize, T) {
    let zero = T::default();
    let mut degree: usize = 0;
    let mut coefficient = T::default();
    for (i, &c) in x.iter().enumerate() {
        if !c.equal(zero) {
            degree = i;
            coefficient = c;
        }
    }
    (degree, coefficient)
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
/// Returns `true` if `v` is all zero, and `false` otherwise.
/// Note: this is not constant-time.
pub(crate) fn is_zero<T: Numeric + Copy>(v: &[T]) -> bool {
    for &x in v {
        if !x.equal(T::default()) {
            return false;
        }
    }
    true
}
