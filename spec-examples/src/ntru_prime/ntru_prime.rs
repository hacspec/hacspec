use hacspec::prelude::*;

/// Struct to decide NtruVersion
pub struct NtruVersion {
    p: usize,
    q: i128,
    w: i128,
}
#[macro_export]
macro_rules! ntru_v {
    ($t:expr) => {{
        if $t == -1 {
            NtruVersion {
                p: 7,
                q: 97,
                w: 4,
            }
        }
        else if $t == 0 {
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
fn create_rand_poly(w: i128, h_deg: usize) -> Seq<i128> {
    let mut counter: usize = 0;
    let mut pos;
    let mut polynom: Seq<i128> = Seq::new(h_deg + 1);

    for _ in 0..h_deg * h_deg * h_deg * h_deg *h_deg *h_deg {
        pos = rand::thread_rng().gen_range(0, h_deg);
        let c_val = rand::thread_rng().gen_range(0, 2);
        //check if value already contained
        if polynom[pos] == 0 {
            polynom[pos] =  2 * c_val - 1;
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
    modulus: i128,
) -> (Seq<i128>, Result<Seq<i128>, &'static str>) {
    let f: Seq<i128> = create_rand_poly(n.w, n.p);
    let mut irr: Seq<i128> = Seq::new(n.p + 1);
    irr[0] = - 1 as i128;
    irr[1] = - 1 as i128;
    irr[n.p] = 1 as i128;
    let x = eea(&f, &irr, modulus);
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
    let f_3times = add_poly(&f, &add_poly(&f, &f, n_v.q), n_v.q);
    let mut irr: Seq<i128> = Seq::new(n_v.p + 1);
    irr[0] = - 1 as i128;
    irr[1] = - 1 as i128;
    irr[n_v.p] = 1 as i128;

    let f_3times_pre_inv = eea(&f_3times,&irr,n_v.q);
    let mut f_inv_3times:Seq<i128> = Seq::new(n_v.p + 1);
    match f_3times_pre_inv {
        Ok(v) => {
            f_inv_3times = v;
        }
        Err(_) => println!("Key generating, failed")
    }
    let h = mul_poly_irr(&poly_g.0, &f_inv_3times, &irr,n_v.q);
    // test h is invertable
    assert_eq!(test_h_invertable(&h,n_v.q),true);

    (h, (f, g_inv))
}

// r is the plaintext, h is the public key
fn encryption(r: &Seq<i128>, h: Seq<i128>, n_v: &NtruVersion) -> Seq<i128> {
    let mut irr: Seq<i128> = Seq::new(n_v.p + 1);
    irr[0] = - 1 as i128;
    irr[1] = - 1 as i128;
    irr[n_v.p] = 1 as i128;
    let pre = &mul_poly_irr(r, &h, &irr, n_v.q);
    println!("{:?} * {:?} =  {:?}",r,&h,pre);
    round(pre,3)
}

fn decryption(c: Seq<i128>, key: (Seq<i128>, Seq<i128>), n_v: &NtruVersion) -> Seq<i128> {
    let f = key.0;
    let v = key.1;

    // irr Konstant machen!
    let mut irr: Seq<i128> = Seq::new(n_v.p + 1);
    irr[0] = -1 as i128;
    irr[1] = -1 as i128;
    irr[n_v.p] = 1 as i128;

    // calculate 3*f and 3*f*c
    let f_3 = add_poly(&f, &add_poly(&f, &f, n_v.q), n_v.q);
    let f_3_c = mul_poly_irr(&f_3, &c, &irr, n_v.q);

    // lift f_3_c to R_3
    let mut e = Seq::from_seq(&f_3_c);
    //identity
    let mut identity:Seq<i128> = Seq::new(n_v.p +1);
    identity[0] = 1 as i128;
    e = mul_poly_irr(&e, &identity, &irr, 3);
    //lift to R TODO ändere modulo
    let v_e = mul_poly_irr(&v, &e, &irr,3);
    mul_poly_irr(&v_e,&identity , &irr, 0)
}
