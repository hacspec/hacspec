///! 
///! A set of mathematical utility functions.
///! 
use crate::prelude::*;

#[inline]
pub fn poly_sub<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
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
pub fn poly_add<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
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

/// Polynomial multiplication using operand scanning without modulo.
#[inline]
pub(crate) fn poly_mul_plain<T: Numeric + Copy>(x: &[T], y: &[T], _n: T) -> Vec<T> {
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
pub(crate) fn poly_mul_op_scanning<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
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
pub fn poly_mul<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Vec<T> {
    let mut out = vec![T::default(); x.len() + y.len()];
    for adx in x
        .iter()
        .enumerate()
        .map(|(i, x)| (i, x))
        .filter(|(_, &x)| !x.equal(T::default()))
    {
        for bdx in y
            .iter()
            .enumerate()
            .map(|(i, x)| (i, x))
            .filter(|(_, &x)| !x.equal(T::default()))
        {
            out[adx.0 + bdx.0] = out[adx.0 + bdx.0].add_mod(adx.1.mul_mod(*bdx.1, n), n);
        }
    }
    out
}

/// Euclidean algorithm to compute quotient `q` and remainder `r` of x/y.
/// The length of x and degree of y are assumed to be public
///
/// Returns Ok(quotient, remainder) or Err("Can't divide these two polynomials")
///
#[inline]
pub fn poly_div<T: Numeric + Copy>(x: &[T], y: &[T], n: T) -> Result<(Vec<T>, Vec<T>), &'static str> {
    let (x, y) = normalize(x, y);
    let mut rem = x.clone();
    let mut quo = vec![T::default(); x.len()];
    let (yd, c) = leading_coefficient(&y);
    let dist = x.len() - yd;
    let rlen = rem.len();
    for i in 0..dist {
        let idx = rlen - 1 - i;
        let t = if n.equal(T::default()) {
            // In ℤ we try this. It might not work.
            rem[idx].divide(c) // XXX: Update once we change to Numeric
        } else {
            // divide by using inverse mod n
            rem[idx] * T::inv(c, n)
        };
        if t.equal(T::default()) && !rem[idx].equal(T::default()) {
            return Err("Can't divide these two polynomials");
        }
        let s = monomial(t, dist - i - 1);
        let sy = poly_mul(&s[..], &y[..], n);
        quo = poly_add(&quo[..], &s[..], n);
        rem = poly_sub(&rem, &sy, n);
    }
    Ok((quo, make_fixed_length(&rem, yd)))
}

/// Extended euclidean algorithm to compute the inverse of x in ℤ/n
///
/// **Panics** if x is not invertible.
///
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub(crate) fn extended_euclid_invert<T: Integer + Copy>(x: T, n: T, signed: bool) -> T {
    let mut t = T::ZERO();
    let mut r = n;
    let mut new_t = T::ONE();
    let mut new_r = x;

    println!("n: {:?}", n);
    while !new_r.equal(T::ZERO()) {
        let q: T = r.divide(new_r);

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

/// Subtract quotient (bn/x^bd) from (an/x^ad)
fn quot_sub<T: Integer + Copy>(
    an: &[T],
    ad: usize,
    bn: &[T],
    bd: usize,
    n: T,
) -> (Vec<T>, usize) {
    let cd = std::cmp::max(ad, bd);
    let x = monomial(T::ONE(), 1);
    let mut a = an.to_vec();
    let mut b = bn.to_vec();
    for _ in 0..cd - ad {
        //XXX: Any way to write this more nicely?
        a = poly_mul(&a, &x, n);
    }
    for _ in 0..cd - bd {
        //XXX: Any way to write this more nicely?
        b = poly_mul(&b, &x, n);
    }
    (poly_sub(&a, &b, n), cd)
}

/// Divide a by x assuming a is a multiple of x (shift right by one)
fn poly_divx<T: Numeric + Copy>(v: &[T]) -> Vec<T> {
    let mut out = vec![T::default(); v.len() - 1];
    for (a, &b) in out.iter_mut().zip(v.iter().skip(1)) {
        *a = b;
    }
    out
}

/// Iterate division steps in the constant-time polynomial inversion algorithm
/// See Figure 5.1 from https://eprint.iacr.org/2019/266
/// Instead of returning M2kx((u,v,q,r)) in last component, only return v
fn divstepsx<T: Integer + Copy>(
    nn: usize,
    t: usize,
    fin: &[T],
    gin: &[T],
    n: T,
) -> (i128, Vec<T>, Vec<T>, (Vec<T>, usize)) {
    debug_assert!(t >= nn);
    let mut f = fin.to_vec();
    let mut g = gin.to_vec();
    let mut delta = 1;

    // Each of u,v,q,r in (f, i) represents quotient f/x^i
    // u,v,q,r = 1,0,0,1
    let mut u = (vec![T::ONE(); 1], 0);
    let mut v = (vec![T::ZERO(); 1], 0);
    let mut q = (vec![T::ZERO(); 1], 0);
    let mut r = (vec![T::ONE(); 1], 0);

    for i in 0..nn {
        // Bring u,v,q,r back to fixed precision t
        u.0 = make_fixed_length(&u.0, t);
        v.0 = make_fixed_length(&v.0, t);
        q.0 = make_fixed_length(&q.0, t);
        r.0 = make_fixed_length(&r.0, t);

        // Decrease precision of f and g in each iteration
        f = make_fixed_length(&f, nn - i);
        g = make_fixed_length(&g, nn - i);

        // TODO: make swap constant time
        if delta > 0 && !g[0].equal(T::ZERO()) {
            delta = -delta;
            let t = f;
            f = g;
            g = t;
            let t = q;
            q = u;
            u = t;
            let t = r;
            r = v;
            v = t;
        }

        delta = delta + 1;
        let f0 = monomial(f[0], 0);
        let g0 = monomial(g[0], 0);

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

/// Constant-time extended euclidean algorithm to compute the inverse of x in yℤ\[x\]
/// x.len() and degree of y are assumed to be public
/// See recipx in Figure 6.1 of https://eprint.iacr.org/2019/266
#[inline]
pub fn extended_euclid<T: Integer + Copy>(
    x: &[T],
    y: &[T],
    n: T,
) -> Result<Vec<T>, &'static str> {
    let (yd, _) = leading_coefficient(y);
    debug_assert!(yd >= x.len());
    debug_assert!(yd > 0);

    let mut f = make_fixed_length(y, yd + 1);
    f.reverse();
    let mut g = make_fixed_length(x, yd);
    g.reverse();

    let (delta, f, _g, v) = divstepsx(2 * yd - 1, 2 * yd - 1, &f, &g, n);
    if delta != 0 {
        return Err("Could not invert the polynomial");
    }

    let t = monomial(f[0].inv(n), 2 * yd - 2 - v.1);
    let mut rr = poly_mul(&t, &v.0, n);
    rr = make_fixed_length(&rr, yd);
    rr.reverse();
    Ok(rr)
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == 1`.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cswap_bit<T: Integer + Copy>(x: T, y: T, c: T) -> (T, T) {
    cswap(x, y, T::default().wrap_sub(c))
}

/// Conditional, constant-time swapping.
/// Returns `(x, y)` if `c == 0` and `(y, x)` if `c == T::max`.
/// The return value is undefined if `c` has any other value.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cswap<T: Integer + Copy>(x: T, y: T, c: T) -> (T, T) {
    let mask = c & (x ^ y);
    (x ^ mask, y ^ mask)
}

/// Set bit at position `i` in `x` to `b` if `c` is all 1 and return the restult.
/// Returns `x` if `c` is `0`.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cset_bit<T: Integer + Copy>(x: T, b: T, i: usize, c: T) -> T {
    let set = x.set_bit(b, i);
    let (out, _) = cswap(x, set, c);
    out
}

/// Add two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cadd<T: Integer + Copy>(x: T, y: T, c: T) -> T {
    let sum = x.wrap_add(y);
    let (x, _) = cswap(x, sum, c);
    x
}

/// Subtract two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Addition is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn csub<T: Integer + Copy>(x: T, y: T, c: T) -> T {
    let diff = x.wrap_sub(y);
    let (x, _) = cswap(x, diff, c);
    x
}

/// Multiply two numerics if condition `c` is set (all bits 1).
/// Returns `x` if condition `c` is `0`.
/// Note: Multiplication is always wrapping.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn cmul<T: Integer + Copy>(x: T, y: T, c: T) -> T {
    let prod = x.wrap_mul(y);
    let (x, _) = cswap(x, prod, c);
    x
}

/// Constant time division for Numerics.
/// Note that this function is only constant time if `T` is a secret integer and
/// hence provides constant time implementations for the used functions.
#[inline]
#[cfg_attr(feature="use_attributes", library(internal))]
pub fn ct_div<T: Integer + Copy>(a: T, d: T) -> (T, T) {
    let mut q = T::default();
    let mut r = T::default();
    for i in (0..T::NUM_BITS).rev() {
        r = r << 1;
        r = r.set(0, a, i);
        // The code below is equivalent to the following.
        // if r.greater_than_or_qual(d) {
        //     r = r - d;
        //     q = q.set_bit(T::ONE(), i);
        // }
        let geq = r.greater_than_or_equal_bm(d);
        r = csub(r, d, geq);
        q = cset_bit(q, T::ONE(), i, geq);
    }
    (q, r)
}
