///!
///! A set of mathematical utility functions.
///! TODO: T might be a signed integer! Everything in here only considers unsigned really.
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
#[allow(dead_code)]
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
#[allow(dead_code)]
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
/// Convert Seq<u128> to Seq<i128>
pub fn convert_u128_to_i128(sequence: Seq<u128> )-> Seq<i128>{
    let mut result:Seq<i128> = Seq::new(sequence.len());
    for i in 0..sequence.len(){
        result[i] = sequence[i] as i128;
    }
    result
}

/// makes poly to an element of R_modulo \ irr
pub fn R(irr:&Seq<i128>,poly:&Seq<i128>,modulo:i128) -> Seq<u128>{
    let pre = euclidean_division(&poly, &irr, modulo, irr.len()-1).1;
    make_positive(&pre,modulo)

}

/// polynomial multiplication of two size fixed polynomials in R_modulo \ irr
pub fn mul_poly_irr(a:&Seq<i128>,b:&Seq<i128>,irr:&Seq<i128>,modulo:i128) -> Seq<i128>{
    assert!(a.len()==b.len(),true);
    let mut result:Seq<i128> = Seq::new(a.len());
    for i in 0..a.len(){
        if a[i] == 0{
            continue;
        }
        for j in 0..b.len(){
            if b[j] == 0 {
                continue;
            }

            if i + j > a.len() - 2 {
                // modulo irr
                // factor is the coeff
                let factor = a[i] * b[j];
                result[1+((i + j) % (a.len() -1))] = result[1 + (i + j) % (a.len() - 1)] -factor * irr[1];
                result[(i + j) % (a.len() -1)] = result[(i + j) % (a.len() - 1)] -factor * irr[0];
                continue;
            }
            result[i + j] = result[i + j] + a[i] * b[j];
        }
    }
    if modulo > 0 {
        for i in 0..result.len(){
            result[i] = result[i] % modulo;

        }
    }
    convert_u128_to_i128(make_positive(&result,modulo))
}

/// simple schoolbook polynomial multiplication with sparse and all coefficients mod modulo
pub fn mul_poly_naive(a:&Seq<i128>,b:&Seq<i128>,modulo:i128) -> Seq<i128>{
    let mut out:Seq<i128> = Seq::new(a.len()+b.len());
    for i in 0..a.len() {
        if a[i] == 0{
            continue;
        }
        for j in 0..b.len() {
            out[i + j] = (a[i] * b[j] + out[i + j]) % modulo;
        }
    }
    convert_u128_to_i128(make_positive(&out,modulo))
}



/// simple polynomial multiplication for two fixed size polynomials O(n²) with a * b mod modulo
/// Assumption: Degree of a * b < Size of a
pub fn mul_poly(a:&Seq<i128>,b:&Seq<i128>,modulo:i128) -> Seq<i128>{
    assert!(a.len()==b.len(),true);
    let mut result:Seq<i128> = Seq::new(a.len());
    for i in 0..a.len(){
        if a[i] == 0{
            continue;
        }
        for j in 0..b.len(){
            if b[j] == 0{
                continue;
            }
            if i + j > a.len() -1 {
                panic!("Overflow");
            }
            result[i + j] = (result[i + j] + (a[i] * b[j])) % modulo;
        }
    }
    result
}

/// increases size of poly (Seq<i128>) to p
fn monomial_poly(poly:&Seq<i128>,size:usize) ->Seq<i128>{
    let mut result:Seq<i128> = Seq::new(size);
    for i in 0..poly.len(){
        result[i] = poly[i];
    }
    result
}

/// if all coefficients of a polynomial are 0, returns True
/// else false
fn is_empty(poly:&Seq<i128>)->bool{
    let mut result = true;
    for i in 0..poly.len(){
        if poly[i] != 0{
            result = false;
            break;
        }
    }
    result
}
/// returns highes degree of polynomial, e.g. for  3x² + 2x + 1 -> 2
pub fn deg(poly:&Seq<i128>) -> usize{
    let mut deg = 0;
    for i in 0..poly.len()-1{
        if poly[poly.len() - 1 - i] != 0{
            deg = poly.len() - 1 -i;
            break;
        }
    }
    deg
}
/// returns number of coefficient != 0, e.g. for  -3x⁵ + 3x² + 2x + 1 -> 4
pub fn weight(poly:&Seq<i128>)->usize{
    let tmp = Seq::from_seq(poly);
    let mut weight = 0;
    for i in 0..tmp.len(){
        if tmp[i] != 0{
            weight = weight + 1;
        }
    }
    weight
}

/// returns coefficient of the highest degree, e.g. for  3x² + 2x + 1 -> 3
pub fn leading_coef(poly:&Seq<i128>) -> i128{
    poly[deg(poly)]
}

/// makes coefficients positiv, e.g. -3 mod 4 = 1
pub fn make_positive(poly:&Seq<i128>, q:i128)-> Seq<u128>{
    let mut result = Seq::new(poly.len());
    for i in 0..poly.len(){
        if poly[i] < 0 {
        result[i] = (poly[i] + q) as u128;
        }else {
        result[i] = poly[i] as u128;
        }
    }
    result
}

/// Polynomial Addition, calculates a + b mod modulo
/// if mono=True it add two polynomials/ Seq<i128> which haven't the same size
pub fn add_poly(a:&Seq<i128>, b:&Seq<i128>, modulo:i128,mono:bool)->Seq<i128>{
    let mut x = Seq::from_seq(a);
    let  mut y = Seq::from_seq(b);
    if mono && a.len() < b.len() {
        x = monomial_poly(a,b.len());
    }else if mono{
        y = monomial_poly(b,a.len());
    }
    let mut result = Seq::from_seq(&x);
    for i in 0..result.len(){
        result[i] = (result[i] + y[i]) % modulo;
    }
    convert_u128_to_i128(make_positive(&result,modulo))

}
/// polynomial subtraction, calculates a - b mod modulo
/// if mono=True it subtract two polynomials/ Seq<i128> which haven't the same size
pub fn sub_poly(a:&Seq<i128>, b:&Seq<i128>, modulo:i128,mono:bool)->Seq<i128>{
    let mut x = Seq::from_seq(a);
    let mut y = Seq::from_seq(b);
    if mono && a.len() < b.len(){
        x = monomial_poly(a,b.len());
    }else if mono{
        y = monomial_poly(b,a.len());
    }
    let mut result = Seq::from_seq(&x);
    for i in 0..result.len(){
        result[i] = (result[i] - y[i]) % modulo ;
    }
    convert_u128_to_i128(make_positive(&result,modulo))
}


/// floor division for i128
fn div(a:i128,b:i128)->i128{
    let mut result = 0;
    let mut tmp = b;
    while a >= tmp{
        tmp = tmp + b;
        result = result + 1;
    }
    result
}

/// return the inverse of a mod m, Fermat's little theorem
/// Necessary Assumption m is prime and a < m
fn invert_fermat(a:i128, m:i128)->i128{
    power(a, m-2,m)
}
/// calculates x^y mod m
fn power(x:i128,y:i128,m:i128)->i128{
    if y == 0{
        return 1;
    }
    let mut p = power(x, div(y,2), m) % m;
    p = (p * p) % m;

    if y % 2 == 0 {
        return p;
    }

    return (x * p) % m
}
/// scalar division in R_p, calculates a / scalar mod p
fn scalar_div(a:&Seq<i128>,scalar:i128,p: i128)->Seq<i128>{
    let mut result = Seq::from_seq(a);
    let inv = invert_fermat(scalar, p);
    for i in 0..a.len(){
        result[i] = (result[i] * inv) % p;
    }
    result
}
/// euclidean polynomial division, calculates a/ b in R_modulo
/// returns fixed size polynomial ( size is p)
pub fn euclidean_division(a:&Seq<i128>, b: &Seq<i128>, modulo : i128, p : usize) -> (Seq<i128>,Seq<i128>){
    let mut r:Seq<i128> = Seq::from_seq(a);
    let mut q:Seq<i128> = Seq::new(p+1);
    if deg(&b) == 0{
        return (scalar_div(&r,b[0], modulo),q);
    }
    let u = invert_fermat(leading_coef(b),modulo);
    let d = deg(&b);
    while deg(&r) >= d {
        let mut s:Seq<i128> = Seq::new(deg(&r)-d +1);
        s[deg(&r) - d] = leading_coef(&r) * u;
        q = add_poly(&q,&s,modulo,true);
        r = sub_poly(&r,&mul_poly_naive(&s,&b,modulo),modulo,true);
    }
    r = convert_u128_to_i128(make_positive(&r,modulo));
    q = convert_u128_to_i128(make_positive(&q,modulo));

    // back to right len
    let mut q_right:Seq<i128> = Seq::new(b.len());
    let mut r_right = Seq::from_seq(&q_right);
    if deg(&q) > p || deg(&r) > p {
        panic!("Division failed");
    }
    for i in 0..p+1{
        q_right[i] = q[i];
        r_right[i] = r[i];
    }
    (q_right,r_right)

}


/// Extended Euclidean Algorithm on Seq<i128> which returns the inverse of a in R_modulo \ irr.
/// if a has no inverse in R_modulo \ irr, returns Err(string)
pub fn eea(a:&Seq<i128>, irr:&Seq<i128>, modulo:i128) -> Result<Seq<i128>,&'static str>{
    let mut t:Seq<i128> = Seq::new(a.len());
    let mut r = Seq::from_seq(irr);
    let mut new_t =  Seq::new(a.len());
    new_t[0] = 1 as i128;
    let mut new_r = Seq::from_seq(a);
    new_r = convert_u128_to_i128(make_positive(&new_r,modulo));
    let p = irr.len()-1;
    while !is_empty(&new_r){
        let q = euclidean_division(&r,&new_r,modulo,p).0;

        let tmp_t = Seq::from_seq(&new_t);
        new_t = sub_poly(&t,&mul_poly(&q, &new_t, modulo),modulo,false);
        t = Seq::from_seq(&tmp_t);

        let tmp_r = Seq::from_seq(&new_r);
        new_r = sub_poly(&r,&mul_poly(&q, &new_r, modulo),modulo,false);
        r = Seq::from_seq(&tmp_r);

    }
    if deg(&r) > 0 {
        return Err("Not invertable");
    }
    let pre = scalar_div(&t,r[0],modulo);
    let mut result = Seq::from_seq(irr);
    for i in 0..irr.len(){
        result[i] = pre[i];
    }
    Ok(result)
}
