use hacspec::prelude::*;
/// Struct to decide NtruVersion
pub struct NtruVersion {
    pub p: usize,
    pub q: i128,
    pub w: usize,
    pub irr: Seq<i128>,
}
pub fn set_irr(p: usize) -> Seq<i128> {
    let mut irr: Seq<i128> = Seq::new(p + 1);
    irr[0] = -1i128;
    irr[1] = -1i128;
    irr[p] = 1i128;
    irr
}
#[macro_export]
macro_rules! ntru_v {
    ($t:expr) => {{
        if $t == 0 {
            NtruVersion {
                p: 761,
                q: 4591,
                w: 286,
                irr: set_irr(761),
            }
        } else if $t == 1 {
            NtruVersion {
                p: 653,
                q: 4621,
                w: 288,
                irr: set_irr(653),
            }
        } else {
            NtruVersion {
                p: 857,
                q: 5167,
                w: 322,
                irr: set_irr(857),
            }
        }
    }};
}
/// First transform each coefficients to a value between −(q−1)/2 and (q−1)/2
/// then round it to the nearest multiple of 3
pub fn round_to_3(poly:&Seq<i128>, q:i128)->Seq<i128>{
    let mut result = Seq::from_seq(poly);
    let q_12 = (q-1)/2;
    for i in 0..poly.len(){
        if poly[i] > q_12{
            result[i] = poly[i] - q;
        }
    }
    for i in 0..result.len(){
        if result[i] % 3 == 0{
            continue;
        }
        result[i] = result[i] - 1;
        if result[i] % 3 != 0{
            result[i] = result[i] + 2;
        }
    }
    result
}

/// r is the plaintext, h is the public key
pub fn encryption(r: &Seq<i128>, h: Seq<i128>, n_v: &NtruVersion) -> Seq<i128> {
    let pre = mul_poly_irr(r, &h, &n_v.irr, n_v.q);
    round_to_3(&pre, n_v.q)
}

pub fn decryption(c: Seq<i128>, key: (Seq<i128>, Seq<i128>), n_v: &NtruVersion) -> Seq<i128> {
    let f = key.0;
    let v = key.1;
    // calculate 3*f and 3*f*c
    let f_c = mul_poly_irr(&f, &c, &n_v.irr, n_v.q);
    let mut f_3_c = convert_u128_to_i128(R(
        &n_v.irr,
        &add_poly(&f_c, &add_poly(&f_c, &f_c, n_v.q, false), n_v.q, false),
        n_v.q,
    ));
    // view coefficients as values between -(q-1/2) and (q-1/2)

    let q_12 = (n_v.q - 1) / 2;
    for i in 0..f_3_c.len() {
        if f_3_c[i] > q_12 {
            f_3_c[i] = f_3_c[i] - n_v.q;
        }
    }
    // lift f_3_c to R_3
    let mut e: Seq<i128> = Seq::new(f_3_c.len());
    for i in 0..e.len() {
        e[i] = f_3_c[i] % 3;
    }
    e = convert_u128_to_i128(make_positive(&e, 3));
    // calculate e * v in R
    let mut r = mul_poly_irr(&e, &v, &n_v.irr, 3);
    // to R_short
    for i in 0..r.len() {
        if r[i] == 2 {
            r[i] = -1 as i128;
        }
    }
    r
}
