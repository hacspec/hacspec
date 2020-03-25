#![allow(dead_code)]

//!
//! # Polynomials
//!
//! This module implements polynomials ℤn\[x\]/mℤ\[x\].
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

use rand::Rng;
use std::ops::{Add, Div, Mul, Sub};

use crate::integer::*;
use crate::seq::*;
use crate::public_seq::*;

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
fn make_fixed_length<T: TRestrictions<T>>(v: &[T], t: usize) -> Vec<T> {
    let mut out = vec![T::default(); t];
    for (a, &b) in out.iter_mut().zip(v.iter()) {
        *a= b;
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
pub(crate) fn poly_mul_plain<T: TRestrictions<T>>(x: &[T], y: &[T], _n: T) -> Vec<T> {
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
/// The length of x and degree of y are assumed to be public
///
/// Returns (quotient, remainder)
///
/// **Panics** when division isn't possible.
///
#[inline]
pub fn poly_div<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> (Vec<T>, Vec<T>) {
    let (x, y) = normalize(x, y);
    let mut rem = x.clone();
    let mut quo = vec![T::default(); x.len()];
    let (yd, c) = leading_coefficient(&y);
    let dist = x.len() - yd;
    let rlen = rem.len();
    for i in 0..dist {
        let idx = rlen - 1 - i;
        let t = if n == T::default() {
            // In ℤ we try this. It might not work.
            rem[idx] / c // XXX: Update once we change to Numeric
        } else {
            // divide by using inverse mod n
            rem[idx] * T::invert(c, n)
        };
        if t == T::default() && rem[idx] != T::default() {
            panic!("Can't divide these two polynomials");
        }
        let s = monomial(t, dist-i-1);
        let sy = poly_mul(&s[..], &y[..], n);
        quo = poly_add(&quo[..], &s[..], n);
        rem = poly_sub(&rem, &sy, n);
    }
    (quo, make_fixed_length(&rem, yd))
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
    v.iter().map(|&x| T::invert(x, n)).collect::<Vec<T>>()
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

/// Subtract quotient (bn/x^bd) from (an/x^ad)
fn quot_sub<T: TRestrictions<T>>(an: &[T], ad: usize, bn: &[T], bd: usize, n: T) -> (Vec<T>, usize){
    let cd = std::cmp::max(ad, bd);
    let x = monomial(T::from_literal(1),1);
    let mut a = an.to_vec();
    let mut b = bn.to_vec();
    for _ in 0..cd-ad {           //XXX: Any way to write this more nicely?
        a = poly_mul(&a, &x, n);
    }
    for _ in 0..cd-bd {           //XXX: Any way to write this more nicely?
        b = poly_mul(&b, &x, n);
    }
    (poly_sub(&a, &b, n), cd)
}

/// Divide a by x assuming a is a multiple of x (shift right by one)
fn poly_divx<T: TRestrictions<T>>(v: &[T]) -> Vec<T> {
    let mut out = vec![T::default(); v.len()-1];
    for(a, &b) in out.iter_mut().zip(v.iter().skip(1)) {
        *a = b;
    }
    out
}

/// Iterate division steps in the constant-time polynomial inversion algorithm
/// See Figure 5.1 from https://eprint.iacr.org/2019/266
/// Instead of returning M2kx((u,v,q,r)) in last component, only return v
fn divstepsx<T: TRestrictions<T>>(nn: usize, t: usize, fin: &[T], gin: &[T], n: T) -> (i128, Vec<T>, Vec<T>, (Vec<T>, usize)) {
    debug_assert!(t >= nn);
    let mut f = fin.to_vec();
    let mut g = gin.to_vec();
    let mut delta = 1;

    // Each of u,v,q,r in (f, i) represents quotient f/x^i
    // u,v,q,r = 1,0,0,1
    let mut u = (vec![T::from_literal(1); 1], 0);
    let mut v = (vec![T::default(); 1], 0);
    let mut q = (vec![T::default(); 1], 0);
    let mut r = (vec![T::from_literal(1); 1], 0);

    for i in 0..nn {
        // Bring u,v,q,r back to fixed precision t
        u.0 = make_fixed_length(&u.0, t);
        v.0 = make_fixed_length(&v.0, t);
        q.0 = make_fixed_length(&q.0, t);
        r.0 = make_fixed_length(&r.0, t);

        // Decrease precision of f and g in each iteration
        f = make_fixed_length(&f, nn-i);
        g = make_fixed_length(&g, nn-i);

        // TODO: make swap constant time
        if delta > 0  && g[0] != T::default() {
            delta = -delta;
            let t = f; f = g; g = t;
            let t = q; q = u; u = t;
            let t = r; r = v; v = t;
        }

        delta = delta+1;
        let f0 = monomial(f[0],0);
        let g0 = monomial(g[0],0);

        // g = (f0*g-g0*f)/x
        let t0 = poly_mul(&f0, &g, n);
        let t1 = poly_mul(&g0, &f, n);
        g = poly_sub(&t0, &t1, n);
        g = poly_divx(&g);

        // q = (f0*q-g0*u)/x
        let t0 = poly_mul(&f0, &q.0, n);
        let t1 = poly_mul(&g0, &u.0, n);
        q = quot_sub(&t0, q.1, &t1, u.1, n);
        q.1 += 1;

        // r = (f0*r-g0*v)/x
        let t0 = poly_mul(&f0, &r.0, n);
        let t1 = poly_mul(&g0, &v.0, n);
        r = quot_sub(&t0, r.1, &t1, v.1, n);
        r.1 += 1;
    }
    (delta, f, g, v)
}

/// Constant-time extended euclidean algorithm to compute the inverse of x in yℤ[x]
/// x.len() and degree of y are assumed to be public
/// See recipx in Figure 6.1 of https://eprint.iacr.org/2019/266
#[inline]
pub fn extended_euclid<T: TRestrictions<T>>(x: &[T], y: &[T], n: T) -> Result<Vec<T>, &'static str> {
    let (yd, _) = leading_coefficient(y);
    debug_assert!(yd >= x.len());
    debug_assert!(yd > 0);

    let mut f = make_fixed_length(y, yd+1);
    f.reverse();
    let mut g = make_fixed_length(x, yd);
    g.reverse();

    let (delta,f,g,v) = divstepsx(2*yd-1,2*yd-1,&f,&g, n);
    if delta != 0 {
        return Err("Could not invert the polynomial");
    }

    let t  = monomial(T::invert(f[0],n), 2*yd-2-v.1);
    let mut rr = poly_mul(&t, &v.0, n);
    rr = make_fixed_length(&rr, yd);
    rr.reverse();
    Ok(rr)
}

#[macro_export]
macro_rules! poly {
    ($name:ident, $t:ty, $l:expr, $n:expr, $m:expr) => {
        /// The poly struct for fixed-length polynomials.
        /// Every polynomial is over ℤn[x]/mℤ[x] and reduced by mℤ[x].
        #[derive(Clone, Copy)]
        struct $name {
            poly: [$t; $l],
            irr: [$t; $l + 1],
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
                let mut irr = [<$t>::default(); $l + 1];
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
                let mut irr = [<$t>::default(); $l + 1];
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
                let mut irr = [<$t>::default(); $l + 1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                let mut rng = rand::thread_rng();
                let p_vec: Vec<$t> = (0..$l).map(|_| rng.gen_range(0, $n)).collect();
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
                let mut irr = [<$t>::default(); $l + 1];
                for c in $m.iter() {
                    irr[c.0] = c.1;
                }
                $name {
                    poly: p,
                    irr: irr,
                    n: $n,
                }
            }
        }

        impl fmt::Debug for $name {
            // TODO: ugh
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                "poly: ".fmt(f).unwrap();
                self.poly.iter().collect::<Vec<_>>().fmt(f).unwrap();
                ", irr: ".fmt(f).unwrap();
                self.irr.iter().collect::<Vec<_>>().fmt(f).unwrap();
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
                let r = poly_div(&tmp, &self.irr, self.n).1;
                Self::from(r)
            }
        }

        /// Polynomial division on ℤn[x]/mℤ[x]
        impl Div for $name {
            type Output = (Self, Self);
            fn div(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = poly_div(&self.poly, &rhs.poly, self.n);
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
impl<T: TRestrictions<T>> Div for PublicSeq<T> {
    type Output = (Self, Self);
    fn div(self, rhs: Self) -> Self::Output {
        let r = poly_div(&self.b, &rhs.b, T::default());
        (Self { b: r.0, idx: 0 }, Self { b: r.1, idx: 0 })
    }
}


/// Polynomial multiplication on ℤ[x]
impl<T: TRestrictions<T>> Mul for PublicSeq<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_mul(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial subtraction on ℤ[x]
impl<T: TRestrictions<T>> Sub for PublicSeq<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_sub(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}

/// Polynomial addition on ℤ[x]
impl<T: TRestrictions<T>> Add for PublicSeq<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            b: poly_add(&self.b, &rhs.b, T::default()),
            idx: 0,
        }
    }
}
