#![allow(dead_code)]

//!
//! # Polynomials
//!
//! This module implements polynomials ℤn[x]/mℤ[x].
//! Polynomials are variable sized only for now.
//!
//! Coefficients are currently stored as u128 or i128.
//!
//! **TODO: If necessary, we could extend the definition to larger integers.**
//!
//! Three different types of polynomials are supported:
//! * Polynomial rings over ℤ
//! * Quotient ring over ℤn
//! * Quotient ring over ℤn/mℤ
//!
//! # Polynomial rings over ℤ
//! This most basic form is implemented over basic sequences `Seq<T>`.
//! Addition, Subtraction, Multiplication, and Division with remainder are supported.
//!
//! **Note:** This is currently only implemented for `Seq<u128>` and `Seq<i128>`.
//!

use std::ops::{Add, Div, Mul, Sub};
use rand::Rng;

use crate::seq::*;
use crate::integer::*;

///! First we implement all functions on slices of T.
///! Note that this is equivalent to ℤn[x] (or ℤ[x] depending, depending on T).

/// Rust's built-in modulo (x % n) is signed. This lifts x into ℤn+.
#[inline]
pub(crate) fn signed_mod(x: i128, n: i128) -> i128 {
    let mut ret = x % n;
    while ret < 0 {
        ret += n;
    }
    ret
}

#[inline]
fn pad<T: TRestrictions<T>>(v: &[T], l: usize) -> Vec<T> {
    let mut out = v.to_vec();
    for _ in out.len()..l {
        out.push(T::default());
    }
    out
}

#[inline]
fn truncate<T: TRestrictions<T>>(v: &[T]) -> Vec<T> {
    let (d, c) = leading_coefficient(v);
    println!("d: {:?}, c: {:x?}", d, c);
    let mut out = vec![T::default(); d + 1];
    for (a, &b) in out.iter_mut().zip(v.iter()) {
        *a = b;
    }
    out
}

#[inline]
fn monomial<T>(c: T, d: usize) -> Vec<T>
where
    T: TRestrictions<T>,
{
    let mut p = vec![T::default(); d + 1];
    p[d] = c;
    p
}

#[inline]
fn normalize<T: TRestrictions<T>>(x: &[T], y: &[T]) -> (Vec<T>, Vec<T>) {
    let max_len = std::cmp::max(x.len(), y.len());
    (pad(x, max_len), pad(y, max_len))
}

#[inline]
pub fn leading_coefficient<T: TRestrictions<T>>(x: &[T]) -> (usize, T) {
    let zero = T::default();
    let mut degree: usize = 0;
    let mut coefficient = T::default();
    for (i, &c) in x.iter().enumerate() {
        if c != zero {
            degree = i;
            coefficient = c;
        }
    }
    (degree, coefficient)
}

#[inline]
pub fn poly_sub<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let (x, y) = normalize(x, y);
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        *a = b.sub_mod(c, n);
    }
    out
}

#[inline]
pub fn poly_add<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let (x, y) = normalize(x, y);
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        *a = b.add_mod(c, n);
    }
    out
}

/// Polynomial multiplication using operand scanning without modulo.
#[inline]
pub(crate) fn poly_mul_plain<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let mut out = vec![T::default(); x.len() + y.len()];
    for i in 0..x.len() {
        for j in 0..y.len() {
            out[i + j] = out[i + j] + x[i] * y[j];
        }
    }
    out
}

/// Polynomial multiplication using operand scanning.
/// This is very inefficient and prone to side-channel attacks.
#[inline]
pub(crate) fn poly_mul_op_scanning<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let mut out = vec![T::default(); x.len() + y.len()];
    for i in 0..x.len() {
        for j in 0..y.len() {
            out[i + j] = out[i + j].add_mod(x[i].mul_mod(y[j], n), n);
        }
    }
    out
}

/// Polynomial multiplication using sparse multiplication.
/// This can be more efficient than operand scanning but also prone to side-channel
/// attacks.
#[inline]
pub fn poly_mul<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let mut out = vec![T::default(); x.len() + y.len()];
    for adx in x
        .iter()
        .enumerate()
        .map(|(i, x)| (i, x))
        .filter(|(_, &x)| x != T::default())
    {
        for bdx in y
            .iter()
            .enumerate()
            .map(|(i, x)| (i, x))
            .filter(|(_, &x)| x != T::default())
        {
            out[adx.0 + bdx.0] = out[adx.0 + bdx.0].add_mod(adx.1.mul_mod(*bdx.1, n), n);
        }
    }
    out
}

#[inline]
pub fn random_poly<T: TRestrictions<T>>(l: usize, min: i128, max: i128) -> Seq<T> {
    let mut rng = rand::thread_rng();
    (0..l)
        .map(|_| T::from_signed_literal(rng.gen_range(min, max)))
        .collect::<Vec<T>>()
        .into()
}

/// Euclidean algorithm to compute quotient `q` and remainder `r` of x/y.
///
/// Returns (quotient, remainder)
///
/// **Panics** when division isn't possible.
///
#[inline]
pub fn euclid_div<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> (Vec<T>, Vec<T>) {
    let (x, y) = normalize(x, y);
    let mut q = vec![T::default(); x.len()];
    let mut r = x.clone();
    let (d, c) = leading_coefficient(&y);
    let (mut r_d, mut r_c) = leading_coefficient(&r);

    let mut i = 0;

    while r_d >= d && !is_zero(&r) {
        let idx = r_d - d;

        let c_idx = if n == T::default() {
            // In ℤ we try this. It might not work.
            r_c / c
        } else {
            // r_c / c in ℤn is r_c * 1/c.
            r_c * T::inv(c, n)
        };
        if c_idx == T::default() {
            panic!("c_idx is 0; can't divide these two polynomials");
        }

        let s = monomial(c_idx, idx);
        q = poly_add(&q[..], &s[..], n);
        let sy = poly_mul(&s[..], &y[..], n);
        r = poly_sub(&r, &sy, n);

        let tmp = leading_coefficient(&r);
        r_d = tmp.0;
        r_c = tmp.1;
    }

    (q, r)
}

#[inline]
fn is_zero<T: TRestrictions<T>>(v: &[T]) -> bool {
    for &x in v {
        if x != T::default() {
            return false;
        }
    }
    return true;
}

#[inline]
fn poly_z_inv<T: TRestrictions<T>>(v: &[T], n: T) -> Vec<T> {
    v.iter().map(|&x| T::inv(x, n)).collect::<Vec<T>>()
}

/// Extended euclidean algorithm to compute the inverse of x in ℤ/n
///
/// **Panics** if x is not invertible.
///
#[inline]
pub(crate) fn extended_euclid_invert<T: TRestrictions<T>>(x: T, n: T, signed: bool) -> T {
    let mut t = T::default();
    let mut r = n;
    let mut new_t = T::from_literal(1);
    let mut new_r = x;

    while new_r != T::default() {
        let q: T = r / new_r;

        let tmp = new_r.clone();
        new_r = r.sub_lift(q * new_r, n);
        r = tmp;

        let tmp = new_t.clone();
        new_t = t.sub_lift(q * new_t, n);
        t = tmp;
    }

    if r > T::from_literal(1) && x != T::default() {
        panic!("{:x?} is not invertible in ℤ/{:x?}", x, n);
    }
    println!("xeucl: {:?}", t);
    if t < T::default() {
        if signed {
            t = t.abs()
        } else {
            t = t + n
        };
    };

    t
}

/// Extended euclidean algorithm to compute the inverse of x in yℤ[x]
#[inline]
pub fn extended_euclid<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Result<Vec<T>, &'static str> {
    let (x, y) = normalize(x, y);
    println!("euclid: {:?} / {:?}", x, y);

    let mut new_t = vec![T::default(); x.len()];
    new_t[0] = T::from_literal(1);

    let mut new_r = x.clone();

    let mut t = vec![T::default(); x.len()];
    let mut r = y.clone();

    while !is_zero(&new_r) {
        println!("{:?} / {:?}", r, new_r);
        let q = euclid_div(&r, &new_r, n).0;

        let tmp = new_r.clone();
        new_r = poly_sub(&r, &poly_mul(&q, &new_r, n), n);
        r = tmp;

        let tmp = new_t.clone();
        new_t = poly_sub(&t, &poly_mul(&q, &new_t, n), n);
        t = tmp;
    }

    if leading_coefficient(&r).0 > 0 {
        return Err("Could not invert the polynomial");
    }

    Ok(poly_mul(&t, &poly_z_inv(&r, n), n))
}

#[macro_export]
macro_rules! poly {
    ($name:ident, $t:ty, $l:expr, $n:expr, $m:expr) => {
        /// The poly struct for fixed-length polynomials.
        /// Every polynomial is over ℤn[x]/mℤ[x] and reduced by mℤ[x].
        #[derive(Clone, Copy)]
        struct $name {
            poly: [$t; $l],
            irr: [$t; $l+1],
            n: $t,
        }
        impl $name {
            /// Get a new sparse polynomial.
            /// For other polynomials use `new_full`.
            fn new(p: &[(usize, $t)]) -> $name {
                let mut poly = [<$t>::default(); $l];
                for c in p.iter() {
                    poly[c.0] = c.1;
                }
                let mut irr = [<$t>::default(); $l+1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                Self {
                    poly: poly,
                    irr: irr,
                    n: $n,
                }
            }
            /// Get a new polynomial from a full array with coefficients.
            fn new_full(p: [$t; $l]) -> $name {
                let mut irr = [<$t>::default(); $l+1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                Self {
                    poly: p,
                    irr: irr,
                    n: $n,
                }
            }
            /// Generate a random polynomial with coefficients between 0 and $n.
            fn random() -> $name {
                let mut irr = [<$t>::default(); $l+1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                let mut rng = rand::thread_rng();
                let p_vec: Vec<$t> = (0..$l)
                    .map(|_| rng.gen_range(0, $n))
                    .collect();
                let mut p = [<$t>::default(); $l];
                for (a, b) in p.iter_mut().zip(p_vec.iter()) {
                    *a = *b;
                }
                Self {
                    poly: p,
                    irr: irr,
                    n: $n,
                }
            }
            /// Check if the two polynomials are defined over the same ring.
            /// **Note** This shouldn't work on secret integers.
            fn compatible(&self, other: &Self) -> bool {
                if self.n != other.n {
                    return false;
                }
                if self.irr.len() != other.irr.len() {
                    return false;
                }
                if self.poly.len() != other.poly.len() {
                    // This should be unreachable.
                    return false;
                }
                for (a, b) in self.irr.iter().zip(other.irr.iter()) {
                    if a != b {
                        return false;
                    }
                }
                return true;
            }
            /// Invert this polynomial.
            /// **Panics** if the polynomial is not invertible.
            fn inv(self) -> Self {
                println!("inv {:?}", self);
                Self::from(extended_euclid(&self.poly, &self.irr, self.n).unwrap())
            }
        }

        impl From<Vec<$t>> for $name {
            fn from(v: Vec<$t>) -> $name {
                let (d, _) = leading_coefficient(&v);
                debug_assert!(d <= $l);
                if d > $l {
                    panic!("The vector is too long to fit this polynomial.");
                }
                let mut p = [<$t>::default(); $l];
                for (a, b) in p.iter_mut().zip(v.iter()) {
                    *a = *b;
                }
                let mut irr = [<$t>::default(); $l+1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                $name {
                    poly: p,
                    irr: irr,
                    n: $n
                }
            }
        }

        impl fmt::Debug for $name {
            // TODO: ugh
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                "poly: ".fmt(f).unwrap();
                self.poly
                    .iter()
                    .collect::<Vec<_>>()
                    .fmt(f).unwrap();
                ", irr: ".fmt(f).unwrap();
                self.irr
                    .iter()
                    .collect::<Vec<_>>()
                    .fmt(f).unwrap();
                ", n: ".fmt(f).unwrap();
                self.n.fmt(f)
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                if !self.compatible(other) {
                    return false;
                }
                for (a, b) in self.poly.iter().zip(other.poly.iter()) {
                    if a != b {
                        return false;
                    }
                }
                return true;
            }
        }

        /// Polynomial subtraction
        impl Sub for $name {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = poly_sub(&self.poly, &rhs.poly, self.n);
                Self::from(r)
            }
        }

        /// Polynomial addition
        impl Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = poly_add(&self.poly, &rhs.poly, self.n);
                Self::from(r)
            }
        }

        /// Polynomial multiplication on ℤn[x]/mℤ[x]
        impl Mul for $name {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let tmp = poly_mul(&self.poly, &rhs.poly, self.n);
                let r = euclid_div(&tmp, &self.irr, self.n).1;
                Self::from(r)
            }
        }

        /// Polynomial division on ℤn[x]/mℤ[x]
        impl Div for $name {
            type Output = (Self, Self);
            fn div(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = euclid_div(&self.poly, &rhs.poly, self.n);
                (Self::from(r.0), Self::from(r.1))
            }
        }
    };
}

/// Polynomial multiplication on ℤ[x]
impl<T: TRestrictions<T>> Mul for Seq<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_mul(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial subtraction on ℤ[x]
impl<T: TRestrictions<T>> Sub for Seq<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_sub(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial addition on ℤ[x]
impl<T: TRestrictions<T>> Add for Seq<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_add(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial division on ℤ[x]
impl<T: TRestrictions<T>> Div for Seq<T> {
    type Output = (Self, Self);
    fn div(self, rhs: Self) -> Self::Output {
        let r = euclid_div(&self.b, &rhs.b, T::default());
        (Self { b: r.0, idx: 0 }, Self { b: r.1, idx: 0 })
    }
}
