use crate::prelude::*;

use poly::*;

/// Constant-time extended euclidean algorithm to compute the inverse of x in yℤ\[x\]
/// x.len() and degree of y are assumed to be public
/// See recipx in Figure 6.1 of https://eprint.iacr.org/2019/266
#[inline]
#[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
pub(crate) fn extended_euclid_internal<T: Integer + Copy>(
    x: &[T],
    y: &[T],
    n: T,
) -> Result<Vec<T>, &'static str> {
    let (yd, _) = leading_coefficient(y);
    let (xd, _) = leading_coefficient(x);
    debug_assert!(yd >= xd);
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
            core::mem::swap(&mut f, &mut g);
            core::mem::swap(&mut q, &mut u);
            core::mem::swap(&mut r, &mut v);
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

/// Divide a by x assuming a is a multiple of x (shift right by one)
fn poly_divx<T: Numeric + Copy>(v: &[T]) -> Vec<T> {
    let mut out = vec![T::default(); v.len() - 1];
    for (a, &b) in out.iter_mut().zip(v.iter().skip(1)) {
        *a = b;
    }
    out
}

/// Subtract quotient (bn/x^bd) from (an/x^ad)
fn quot_sub<T: Integer + Copy>(an: &[T], ad: usize, bn: &[T], bd: usize, n: T) -> (Vec<T>, usize) {
    let cd = core::cmp::max(ad, bd);
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
