use hacspec::prelude::*;

/// Struct to decide NtruVersion
pub struct NtruVersion {
    p: usize,
    q: u128,
    w: u128,
}
#[macro_export]
macro_rules! ntru_v {
    ($t:expr) => {{
        if $t == 0 {
            NtruVersion {
                p: 761,
                q: 4591,
                w: 286,
            }
        } else if $t == 1 {
            NtruVersion {
                p: 653,
                q: 4621,
                w: 288,
            }
        } else {
            NtruVersion {
                p: 857,
                q: 5167,
                w: 322,
            }
        }
    }};
}

///This function creates a random polynom with w many -1 or 1 and with the highes degree of h_deg.
fn create_rand_poly(w: u128, h_deg: usize, modulo: u128) -> Seq<u128> {
    let mut counter: usize = 0;
    let mut pos;
    let mut polynom: Seq<u128> = Seq::new(h_deg);
    //TODO outsourcen

    for _ in 0..h_deg * h_deg * h_deg * h_deg {
        pos = rand::thread_rng().gen_range(0, h_deg - 1);
        let c_val = rand::thread_rng().gen_range(0, 2);
        //check if value already contained
        if polynom[pos] == 0 {
            polynom[pos] = (modulo + 2 * c_val - 1) % modulo;
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

fn create_invertable_poly(
    n: &NtruVersion,
    modulus: u128,
) -> (Seq<u128>, Result<Seq<u128>, &'static str>) {
    let f: Seq<u128> = create_rand_poly(n.w, (n.p + 1) as usize, modulus);
    let mut irr: Seq<u128> = Seq::new(f.len());
    irr[0] = modulus - 1;
    irr[1] = modulus - 1;
    irr[f.len() - 1] = 1 as u128;
    let x = eea(&f, &irr, modulus);
    (f, x)
}

pub fn key_gen(n_v: &NtruVersion) -> (Seq<u128>, (Seq<u128>, Seq<u128>)) {
    let q = n_v.q;
    println!("generating key...");

    let mut poly_g = create_invertable_poly(n_v, 3);
    // Nearly a probability of 1 to find an invertable polynom
    let mut g_inv: Seq<u128> = Seq::new(n_v.p + 1);
    for _ in 0..4 {
        match poly_g.1 {
            Ok(v) => {
                g_inv = v;
                break;
            }
            Err(_) => poly_g = create_invertable_poly(n_v, 3),
        }
    }
    let mut poly_f = create_invertable_poly(n_v, 3);
    // Nearly a probability of 1 to find an invertable polynom
    let mut f_inv: Seq<u128> = Seq::new(n_v.p + 1);
    for _ in 0..4 {
        match poly_f.1 {
            Ok(s) => {
                f_inv = s;
                break;
            }
            Err(_) => poly_f = create_invertable_poly(n_v, 3),
        }
    }
    let f_inv_3times = add_poly(&f_inv, &add_poly(&f_inv, &f_inv, n_v.q), n_v.q);
    let mut irr: Seq<u128> = Seq::new(f_inv.len());
    irr[0] = q - 1;
    irr[1] = q - 1;
    irr[f_inv.len() - 1] = 1 as u128;

    let h = mul_poly_irr(&poly_g.0, &f_inv_3times, &irr, n_v.q);
    println!("key Gen done!");
    (h, (poly_f.0, g_inv))
}
// IN PROGRESS (NOT WORKING)
// r is the plaintext, h is the public key
fn encryption(r: &Seq<u128>, h: Seq<u128>, n_v: &NtruVersion) -> Seq<u128> {
    let mut irr: Seq<u128> = Seq::new(n_v.p + 1);
    irr[0] = n_v.q - 1;
    irr[1] = n_v.q - 1;
    irr[n_v.p] = 1 as u128;
    // TODO Round
    mul_poly_irr(r, &h, &irr, n_v.q)
}
// IN PROGRESS (NOT WORKING) 
fn decryption(c: Seq<u128>, key: (Seq<u128>, Seq<u128>), n_v: &NtruVersion) -> Seq<u128> {
    let f = key.0;
    let v = key.1;

    let mut irr: Seq<u128> = Seq::new(n_v.p + 1);
    irr[0] = 2 as u128;
    irr[1] = 2 as u128;
    irr[n_v.p] = 1 as u128;

    let f_3 = add_poly(&f, &add_poly(&f, &f, n_v.q), n_v.q);
    let f_3_c = mul_poly_irr(&f_3, &c, &irr, n_v.q);

    let mut identity: Seq<u128> = Seq::new(n_v.p + 1);
    identity[0] = 1 as u128;
    let e = mul_poly_irr(&identity, &f_3_c, &irr, 3);

    mul_poly_irr(&v, &e, &irr, 3)
}
