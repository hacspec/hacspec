///!
///! A set of mathematical utility functions.
///! TODO: T might be a signed integer! Everything in here only considers unsigned really.
///!
use crate::prelude::*;

mod ct_poly;
pub mod ct_util;
pub mod poly;

use ct_poly::*;
use poly::*;

/// polynomial subtraction, calculates a - b mod modulo
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn sub_poly<T: Numeric + Copy>(a: &Seq<T>, b: &Seq<T>, modulo: T) -> Seq<T> {
    let result = Seq::from_native_slice(&poly_sub(&a.b, &b.b, modulo));
    make_positive(&result, modulo)
}

/// Polynomial Addition, calculates a + b mod modulo
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn add_poly<T: Numeric + Copy>(a: &Seq<T>, b: &Seq<T>, modulo: T) -> Seq<T> {
    let result = Seq::from_native_slice(&poly_add(&a.b, &b.b, modulo));
    make_positive(&result, modulo)
}

/// Simple polynomial multiplication for two fixed size polynomials O(n²) with `a * b mod n`
pub fn mul_poly<T: Numeric + Copy>(a: &Seq<T>, b: &Seq<T>, n: T) -> Seq<T> {
    Seq::from_native_slice(&poly_mul(&a.b, &b.b, n))
}

/// Euclidean polynomial division, calculates `a/b` in `R_n`.
/// Returns `Ok(quotient, remainder)` or `Err("Can't divide these two polynomials")`
pub fn div_poly<T: Integer + Copy>(
    a: &Seq<T>,
    b: &Seq<T>,
    n: T,
) -> Result<(Seq<T>, Seq<T>), &'static str> {
    let (q, r) = poly_div(&a.b, &b.b, n);
    Ok((Seq::from_native_slice(&q), Seq::from_native_slice(&r)))
}

/// Scalar division in `R_p`.
/// Returns `a / scalar mod p`.
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub fn div_scalar<T: Integer + Copy>(a: &Seq<T>, scalar: T, p: T) -> Seq<T> {
    Seq::from_native_slice(&scalar_div(&a.b, scalar, p))
}

/// Returns degree of polynomial, e.g. for  3x² + 2x + 1 -> 2
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn degree_poly<T: Integer + Copy>(poly: &Seq<T>) -> usize {
    deg(&poly.b)
}

/// Euclidean algorithm to compute the inverse of x in yℤ\[x\]
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn extended_euclid<T: Integer + Copy>(
    x: &Seq<T>,
    irr: &Seq<T>,
    n: T,
) -> Result<Seq<T>, &'static str> {
    let result = extended_euclid_internal(&x.b, &irr.b, n)?;
    Ok(Seq::from_native_slice(&result))
}

/// Returns number of coefficient != 0, e.g. for  -3x⁵ + 3x² + 2x + 1 -> 4
pub fn weight<T: Integer + Copy>(poly: &Seq<T>) -> usize {
    let tmp = Seq::from_seq(poly);
    let mut weight = 0;
    for i in 0..tmp.len() {
        if !tmp[i].equal(T::default()) {
            weight = weight + 1;
        }
    }
    weight
}

/// makes coefficients positiv, e.g. -3 mod 4 = 1
pub fn make_positive<T: Numeric + Copy>(poly: &Seq<T>, q: T) -> Seq<T> {
    Seq::from_native_slice(&make_positive_internal(&poly.b, q))
}

/// Extended euclidean algorithm to compute the inverse of x in ℤ/n
///
/// **Panics** if x is not invertible.
///
#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub(crate) fn extended_euclid_invert<T: Integer + Copy>(x: T, n: T, signed: bool) -> T {
    let mut t = T::ZERO();
    let mut r = n;
    let mut new_t = T::ONE();
    let mut new_r = x;

    while !new_r.equal(T::ZERO()) {
        let q: T = r.divide(new_r);

        let tmp = new_r;
        // XXX: a little hacky
        let tmp_prod = q * new_r;
        let mut tmp_r = r;
        while tmp_r.less_than(tmp_prod) {
            tmp_r = tmp_r + n;
        }
        new_r = tmp_r - tmp_prod;
        r = tmp;

        let tmp = new_t;
        // XXX: a little hacky
        let tmp_prod = q * new_t;
        let mut tmp_t = t;
        while tmp_t.less_than(tmp_prod) {
            tmp_t = tmp_t + n;
        }
        new_t = tmp_t - tmp_prod;
        t = tmp;
    }

    if r.greater_than(T::ONE()) && !x.equal(T::ZERO()) {
        panic!("{:x?} is not invertible in ℤ/{:x?}", x, n);
    }
    if t.less_than(T::ZERO()) {
        if signed {
            t = t.absolute()
        } else {
            t = t + n
        };
    };

    t
}

/// Makes poly to an element of R_modulo \ irr
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn poly_to_ring<T: Integer + Copy>(irr: &Seq<T>, poly: &Seq<T>, modulus: T) -> (Seq<T>, bool) {
    match div_poly(&poly, &irr, modulus) {
        Ok(pre) => {
            let pre = pre.1;
            (make_positive(&pre, modulus), true)
        }
        Err(_) => (Seq::new(1usize), false),
    }
}

/// Polynomial multiplication of two size fixed polynomials in R_modulo \ irr
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub fn mul_poly_irr<T: Integer + Copy>(a: &Seq<T>, b: &Seq<T>, irr: &Seq<T>, modulo: T) -> Seq<T> {
    let mut result: Seq<T> = Seq::new(a.len());
    for i in 0..a.len() {
        if a[i].equal(T::default()) {
            continue;
        }
        for j in 0..b.len() {
            if b[j].equal(T::default()) {
                continue;
            }

            if i + j > a.len() - 2 {
                // modulo irr | factor is the coefficient
                let factor = a[i] * b[j];
                result[1 + ((i + j) % (a.len() - 1))] =
                    result[1 + (i + j) % (a.len() - 1)] - factor * irr[1];
                result[(i + j) % (a.len() - 1)] = result[(i + j) % (a.len() - 1)] - factor * irr[0];
                continue;
            }
            result[i + j] = result[i + j] + a[i] * b[j];
        }
    }
    if modulo.greater_than(T::default()) {
        for i in 0..result.len() {
            result[i] = result[i].modulo(modulo);
        }
    }
    make_positive(&result, modulo)
}
