use crate::prelude::*;

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub(crate) fn poly_sub<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let (x, y) = normalize(x, y);
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        if n.equal(T::default()) {
            *a = b - c;
        } else {
            *a = b.sub_mod(c, n);
        }
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub(crate) fn poly_add<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let (x, y) = normalize(x, y);
    debug_assert!(x.len() == y.len());
    let mut out = vec![T::default(); x.len()];
    for (a, (&b, &c)) in out.iter_mut().zip(x.iter().zip(y.iter())) {
        if n.equal(T::default()) {
            *a = b + c;
        } else {
            *a = b.add_mod(c, n);
        }
    }
    out
}

/// Polynomial multiplication using sparse multiplication.
/// This can be more efficient than operand scanning but also prone to side-channel
/// attacks.
#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub(crate) fn poly_mul<T: Numeric + Copy>(a: &[T], b: &[T], n: T) -> Vec<T> {
    let mut result = vec![T::default(); a.len() + b.len()];
    for i in 0..a.len() {
        if !a[i].equal(T::default()) {
            for j in 0..b.len() {
                if !b[j].equal(T::default()) {
                    result[i + j] = (result[i + j].add(a[i] * b[j])).modulo(n);
                }
            }
        }
    }
    result
}

#[inline]
pub(crate) fn poly_div<T: Integer + Copy>(a: &[T], b: &[T], n: T) -> (Vec<T>, Vec<T>) {
    let (a, b) = normalize(a, b);
    let mut r = a.clone();
    let mut q = vec![T::default(); a.len()];
    if deg(&b) == 0 {
        return (scalar_div(&r, b[0], n), q);
    }
    let u = invert_fermat(leading_coef(&b), n);
    let d = deg(&b);
    while deg(&r) >= d {
        let s = monomial(leading_coef(&r) * u, deg(&r) - d);
        q = poly_add(&q, &s, n);
        r = poly_sub(&r, &mul_poly_naive(&s, &b, n), n);
    }

    // If `T` is a signed integer we might want to do this.
    // It's a no-op for unsigned integers.
    r = make_positive_internal(&r, n);
    q = make_positive_internal(&q, n);

    (q, r)
}

/// scalar division in R_p, calculates a / scalar mod p
#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
pub(crate) fn scalar_div<T: Integer + Copy>(a: &[T], scalar: T, p: T) -> Vec<T> {
    let mut result = Vec::new();
    let inv = invert_fermat(scalar, p);
    for &a_i in a.iter() {
        result.push((a_i * inv).modulo(p));
    }
    result
}

pub(crate) fn make_positive_internal<T: Numeric + Copy>(poly: &[T], q: T) -> Vec<T> {
    let mut result = vec![T::default(); poly.len()];
    for i in 0..poly.len() {
        result[i] = poly[i].signed_modulo(q);
    }
    result
}

// --- Internal helpers --- //

/// simple schoolbook polynomial multiplication with sparse and all coefficients mod modulo
#[inline]
#[cfg_attr(feature = "use_attributes", not_hacspec)]
fn mul_poly_naive<T: Integer + Copy>(a: &[T], b: &[T], modulo: T) -> Vec<T> {
    let mut out = vec![T::default(); a.len() + b.len()];
    for i in 0..a.len() {
        if a[i].equal(T::ZERO()) {
            continue;
        }
        for j in 0..b.len() {
            out[i + j] = (a[i] * b[j] + out[i + j]).modulo(modulo);
        }
    }
    make_positive_internal(&out, modulo)
}

/// returns coefficient of the highest degree, e.g. for  3x² + 2x + 1 -> 3
#[inline]
fn leading_coef<T: Integer + Copy>(poly: &[T]) -> T {
    poly[deg(poly)]
}

/// Return the inverse of `a mod m`, Fermat's little theorem
/// Necessary Assumption `m` is prime and `a < m`
#[cfg_attr(feature = "use_attributes", in_hacspec)]
fn invert_fermat<T: Integer + Copy>(a: T, m: T) -> T {
    a.pow_mod(m - T::TWO(), m)
}

pub(crate) fn deg<T: Integer + Copy>(poly: &[T]) -> usize {
    let mut deg = 0;
    for i in 0..poly.len() - 1 {
        if !poly[poly.len() - 1 - i].equal(T::default()) {
            deg = poly.len() - 1 - i;
            break;
        }
    }
    deg
}
