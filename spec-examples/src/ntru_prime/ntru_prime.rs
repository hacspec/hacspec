use hacspec_lib::prelude::*;

/// NtruPrime parameters
pub struct Parameters {
    pub p: usize,
    pub q: i128,
    pub w: usize,
    pub irr: Seq<i128>,
}

/// Positions and coefficients for a polynomial.
pub struct Poly {
    pub positions: Seq<i128>,
    pub coefficients: Seq<i128>,
}

type SecretKey = (Seq<i128>, Seq<i128>);

pub enum Version {
    NtruPrime653,
    NtruPrime761,
    NtruPrime857,
}

fn set_irr(p: usize) -> Seq<i128> {
    let mut irr: Seq<i128> = Seq::new(p + 1);
    irr[0] = -1i128;
    irr[1] = -1i128;
    irr[p] = 1i128;
    irr
}

pub fn get_parameters(v: Version) -> Parameters {
    match v {
        Version::NtruPrime653 => Parameters {
            p: 653,
            q: 4621,
            w: 288,
            irr: set_irr(653),
        },
        Version::NtruPrime761 => Parameters {
            p: 761,
            q: 4591,
            w: 286,
            irr: set_irr(761),
        },
        Version::NtruPrime857 => Parameters {
            p: 857,
            q: 5167,
            w: 322,
            irr: set_irr(857),
        },
    }
}

/// First transform each coefficients to a value between −(q−1)/2 and (q−1)/2
/// then round it to the nearest multiple of 3
pub fn round_to_3(poly: &Seq<i128>, q: i128) -> Seq<i128> {
    let mut result = poly.clone();
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
        result[i] -= 1;
        if result[i] % 3 != 0 {
            result[i] += 2;
        }
    }
    result
}

/// r is the plaintext, h is the public key
pub fn encrypt(r: &Seq<i128>, h: &Seq<i128>, n_v: &Parameters) -> Seq<i128> {
    let pre = mul_poly_irr(r, &h, &n_v.irr, n_v.q);
    round_to_3(&pre, n_v.q)
}

pub fn decrypt(
    c: &Seq<i128>,
    key: &SecretKey,
    n_v: &Parameters,
) -> Result<Seq<i128>, &'static str> {
    let (f, v) = key;

    // calculate 3*f and 3*f*c
    let f_c = mul_poly_irr(&f, &c, &n_v.irr, n_v.q);
    let (mut f_3_c, ok) = poly_to_ring(
        &n_v.irr,
        &add_poly(&f_c, &add_poly(&f_c, &f_c, n_v.q), n_v.q),
        n_v.q,
    );
    // view coefficients as values between -(q-1/2) and (q-1/2)
    let q_12 = (n_v.q - 1) / 2;
    for i in 0..f_3_c.len() {
        if f_3_c[i] > q_12 {
            f_3_c[i] -= n_v.q;
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
    if ok {
        Ok(r)
    } else {
        Err("unable to decrypt")
    }
}

/// This function creates a polynomial with w many -1 or 1 and with the highest degree of h_deg.
/// Randomness of the coefficients and positions has to be provided.
pub fn build_poly(poly: &Poly, h_deg: usize) -> Seq<i128> {
    debug_assert_eq!(poly.coefficients.len(), poly.positions.len());
    let mut polynomial: Seq<i128> = Seq::new(h_deg + 1);

    for i in 0..poly.coefficients.len() {
        polynomial = polynomial.set_chunk(
            1,
            poly.positions[i] as usize,
            &Seq::from_native_slice(&[poly.coefficients[i]]),
        );
    }

    polynomial
}

fn build_invertible_poly(
    poly: &Poly,
    n: &Parameters,
    modulus: i128,
) -> (Seq<i128>, Result<Seq<i128>, &'static str>) {
    let f = build_poly(poly, n.p);
    let x = extended_euclid(&f, &n.irr, modulus);
    (f, x)
}

/// Generate a key from given polynomials `f` and `g`.
/// Generating the polynomials at random has to happen outside.
pub fn key_gen(
    g: &Poly,
    f: &Poly,
    n_v: &Parameters,
) -> Result<(Seq<i128>, SecretKey), &'static str> {
    let poly_g = build_invertible_poly(g, n_v, 3);
    let g_inv = match poly_g.1 {
        Ok(v) => v,
        Err(_) => return Err("This polynomial isn't invertible. Try another one."),
    };

    let f = build_poly(f, n_v.p);

    let f_3times = add_poly(&f, &add_poly(&f, &f, n_v.q), n_v.q);
    let f_3times_pre_inv = extended_euclid(&f_3times, &n_v.irr, n_v.q);
    let f_inv_3times = match f_3times_pre_inv {
        Ok(v) => v,
        Err(_) => return Err("Key generating, failed"),
    };
    let h = mul_poly_irr(&poly_g.0, &f_inv_3times, &n_v.irr, n_v.q);

    Ok((h, (f, g_inv)))
}
