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


/// simple sparse multiplication with modulo irr
pub fn mul_poly_irr(a:&Seq<u128>,b:&Seq<u128>, irr:&Seq<u128>,modulo:u128) -> Seq<u128>{
    assert!(a.len()==b.len(),true);
    let mut result:Seq<u128> = Seq::new(a.len());
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
                let factor = a[i] * b[j];
                result[1+((i + j) % (a.len() -1))] = (result[1 + (i + j) % (a.len() - 1)] + modulo -(factor * irr[1] % modulo)) % modulo;
                result[(i + j) % (a.len() -1)] = (result[(i + j) % (a.len() - 1)] + modulo -(factor * irr[0] % modulo)) % modulo;
                continue;
            }
            result[i + j] = (result[i + j] + (a[i] * b[j])) % modulo;
        }
    }
    result
}


///simple poly multiplication (schoolbook with sparse) O(n²)
fn mul_poly(a:&Seq<u128>,b:&Seq<u128>,modulo:u128) -> Seq<u128>{
    assert!(a.len()==b.len(),true);
    let mut result:Seq<u128> = Seq::new(a.len());
    for i in 0..a.len(){
        if a[i] == 0{
            continue;
        }
        for j in 0..b.len(){
            if i + j > a.len() -1 {
                result[(i + j) % (a.len())] = (result[(i + j) % (a.len())] + (a[i] * b[j])) % modulo;
                continue;
            }
            result[i + j] = (result[i + j] + (a[i] * b[j])) % modulo;
        }
    }
    result
}
fn is_empty(poly:&Seq<u128>)->bool{
    let mut result = true;
    for i in 0..poly.len(){
        if poly[i] != 0{
            result = false;
            break;
        }
    }
    result
}
fn deg(poly:&Seq<u128>) -> usize{
    let mut deg = 0;
    for i in 0..poly.len()-1{
        if poly[poly.len() - 1 - i] != 0{
            deg = poly.len() - 1 -i;
            break;
        }
    }
    deg
}

fn leading_coef(poly:&Seq<u128>) -> u128{
    poly[deg(poly)]
}


pub fn add_poly(a:&Seq<u128>, b:&Seq<u128>, modulo:u128)->Seq<u128>{
    let mut result = Seq::from_seq(b);
    for i in 0..a.len(){
        result[i] = (result[i] + a[i]) % modulo;
    }
    result
}
fn sub_poly(a:&Seq<u128>, b:&Seq<u128>, modulo:u128)->Seq<u128>{
    let mut result = Seq::from_seq(a);
    for i in 0..a.len(){
        while result[i] < b[i]{
            result[i] = result[i] + modulo;
        }
        result[i] = (result[i] - b[i]) % modulo ;
    }
    result
}


/// floor division for u128
fn div(a:u128,b:u128)->u128{
    let mut result = 0;
    let mut tmp = b;
    while a >= tmp{
        tmp = tmp + b;
        result = result + 1;
    }
    result
}

// Some cases are ignored since ntru-prime always use m prime and m >= 2
fn invert_fermat(a:u128, m:u128)->u128{
    power(a, m-2,m)
}

fn power(x:u128,y:u128,m:u128)->u128{
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
fn scalar_div(a:&Seq<u128>,scalar:u128,p: u128)->Seq<u128>{
    let mut result = Seq::from_seq(a);
    let inv = invert_fermat(scalar, p);
    for i in 0..a.len(){

            result[i] = (result[i] * inv) % p;
    }
    result
}



fn division(a:&Seq<u128>, b: &Seq<u128>, p : u128) -> (Seq<u128>,Seq<u128>){

    let mut r:Seq<u128> = Seq::from_seq(a);
    let mut q:Seq<u128> = Seq::new(b.len());
    if deg(&b) == 0{
        return (scalar_div(&r,b[0], p),q);
    }
    let u = invert_fermat(leading_coef(b),p);
    while deg(&r) >= deg(&b){
        let d = deg(&r);
        let mut v:Seq<u128> = Seq::new(a.len());
        v[d - deg(b)] = 1;
        v[d - deg(b)] = u * r[d];
        r = sub_poly(&r, &mul_poly(&v, &b, p), p);
        q = add_poly(&q, &v, p);
    }
    (q,r)

}

pub fn eea(a:&Seq<u128>, b:&Seq<u128>, p:u128) -> Result<Seq<u128>,&'static str>{
    let mut t:Seq<u128> = Seq::new(a.len());
    let mut r = Seq::from_seq(b);
    let mut new_t =  Seq::new(a.len());
    new_t[0] = 1 as u128;
    let mut new_r = Seq::from_seq(a);

    while !is_empty(&new_r){
        let q = division(&r,&new_r,p).0;

        let tmp_t = Seq::from_seq(&new_t);
        new_t = sub_poly(&t,&mul_poly(&q, &new_t, p),p);
        t = Seq::from_seq(&tmp_t);

        let tmp_r = Seq::from_seq(&new_r);
        new_r = sub_poly(&r,&mul_poly(&q, &new_r, p),p);
        r = Seq::from_seq(&tmp_r);

    }
    if deg(&r) > 0 {
        return Err("Not invertable");
    }
    Ok(scalar_div(&t,r[0],p))

}
