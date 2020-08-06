use hacspec::prelude::*;

/// NtruPrime parameters
pub struct Parameters {
    pub p: usize,
    pub q: i128,
    pub w: usize,
    pub irr: Seq<i128>,
}

/// First transform each coefficients to a value between −(q−1)/2 and (q−1)/2
/// then round it to the nearest multiple of 3
pub fn round_to_3(poly: &Seq<i128>, q: i128) -> Seq<i128> {
    let mut result = Seq::from_seq(poly);
    let q_12 = (q - 1) / 2;
    for i in 0..poly.len() {
        if poly[i] > q_12 {
            result[i] = poly[i] - q;
        }
    }
    for i in 0..result.len() {
        if result[i] % 3 == 0 {
            continue;
        }
        result[i] = result[i] - 1;
        if result[i] % 3 != 0 {
            result[i] = result[i] + 2;
        }
    }
    result
}

/// r is the plaintext, h is the public key
pub fn encrypt(r: &Seq<i128>, h: Seq<i128>, n_v: &Parameters) -> Seq<i128> {
    let pre = mul_poly_irr(r, &h, &n_v.irr, n_v.q);
    round_to_3(&pre, n_v.q)
}

pub fn decrypt(c: Seq<i128>, key: (Seq<i128>, Seq<i128>), n_v: &Parameters) -> Seq<i128> {
    let f = key.0;
    let v = key.1;
    // calculate 3*f and 3*f*c
    let f_c = mul_poly_irr(&f, &c, &n_v.irr, n_v.q);
    let mut f_3_c = poly_to_ring(
        &n_v.irr,
        &add_poly(&f_c, &add_poly(&f_c, &f_c, n_v.q), n_v.q),
        n_v.q,
    );
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
    e = make_positive(&e, 3);
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
