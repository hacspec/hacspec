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

use crate::prelude::*;

///! First we implement all functions on slices of T.
///! Note that this is equivalent to ℤn[x] (or ℤ[x] depending, depending on T).

#[macro_export]
macro_rules! poly {
    ($name:ident, $t:ty, $l:expr, $n:expr, $m:expr) => {
        /// The poly struct for fixed-length polynomials.
        /// Every polynomial is over ℤn\[x\]/mℤ\[x\] and reduced by mℤ\[x\].
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
            /// Returns an `Err` if the polynomial is not invertible.
            fn inv(self) -> Result<Self, &'static str> {
                match extended_euclid(&self.poly, &self.irr, self.n) {
                    Ok(v) => Ok(Self::from_vec(v)),
                    Err(e) => Err(e),
                }
            }

            pub fn from_vec(v: Vec<$t>) -> $name {
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
                Self::from_vec(r)
            }
        }

        /// Polynomial addition
        impl Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = poly_add(&self.poly, &rhs.poly, self.n);
                Self::from_vec(r)
            }
        }

        /// Polynomial multiplication on ℤn[x]/mℤ[x]
        impl Mul for $name {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let tmp = poly_mul(&self.poly, &rhs.poly, self.n);
                let r = match poly_div(&tmp, &self.irr, self.n) {
                    Ok(v) => v.1,
                    Err(e) => panic!(e),
                };
                Self::from_vec(r)
            }
        }

        /// Polynomial division on ℤn[x]/mℤ[x]
        impl Div for $name {
            type Output = (Self, Self);
            fn div(self, rhs: Self) -> Self::Output {
                debug_assert!(self.compatible(&rhs));
                let r = match poly_div(&self.poly, &rhs.poly, self.n) {
                    Ok(v) => v,
                    Err(e) => panic!(e),
                };
                (Self::from_vec(r.0), Self::from_vec(r.1))
            }
        }
    };
}
