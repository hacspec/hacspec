use hacspec::prelude::*;

/// Struct to decide NtruVersion
pub struct NtruVersion {
    pub p: usize,
    pub q: i128,
    pub w: i128,
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

///This function creates a random polynom with w many -1 or 1 and with the highes degree of h_deg.
pub fn create_rand_poly(w: i128, h_deg: usize) -> Seq<i128> {
    let mut counter: usize = 0;
    let mut pos;
    let mut polynom: Seq<i128> = Seq::new(h_deg + 1);

    for _ in 0..h_deg * h_deg * h_deg * h_deg * h_deg * h_deg {
        pos = rand::thread_rng().gen_range(0, h_deg);
        let c_val = rand::thread_rng().gen_range(0, 2);
        //check if value already contained
        if polynom[pos] == 0 {
            polynom[pos] = 2 * c_val - 1;
        } else {
            continue;
        }
        counter = counter + 1;

        if counter == w as usize {
            break;
        }
    }
    polynom
}

pub fn create_invertable_poly(
    n: &NtruVersion,
    modulus: i128,
) -> (Seq<i128>, Result<Seq<i128>, &'static str>) {
    let f: Seq<i128> = create_rand_poly(n.w, n.p);
    let x = eea(&f, &n.irr, modulus);
    (f, x)
}

pub fn key_gen(n_v: &NtruVersion) -> (Seq<i128>, (Seq<i128>, Seq<i128>)) {
    let mut poly_g = create_invertable_poly(n_v, 3);
    // Nearly a probability of 1 to find an invertable polynom
    let mut g_inv: Seq<i128> = Seq::new(n_v.p);
    for _ in 0..4 {
        match poly_g.1 {
            Ok(v) => {
                g_inv = v;
                break;
            }
            Err(_) => poly_g = create_invertable_poly(n_v, 3),
        }
    }

    //create f
    let f = create_rand_poly(n_v.w, n_v.p);
    let f_3times = add_poly(&f, &add_poly(&f, &f, n_v.q, false), n_v.q, false);
    let f_3times_pre_inv = eea(&f_3times, &n_v.irr, n_v.q);
    let mut f_inv_3times: Seq<i128> = Seq::new(n_v.p + 1);
    match f_3times_pre_inv {
        Ok(v) => {
            f_inv_3times = v;
        }
        Err(_) => println!("Key generating, failed"),
    }
    let h = mul_poly_irr(&poly_g.0, &f_inv_3times, &n_v.irr, n_v.q);

    (h, (f, g_inv))
}
