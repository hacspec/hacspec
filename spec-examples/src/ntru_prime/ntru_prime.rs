use hacspec::prelude::*;

/// Struct to decide NtruVersion
pub struct NtruVersion {
    pub p: usize,
    pub q: u128,
    pub w: u128,
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
// TODO remove pub
pub fn create_rand_poly(w: u128, h_deg: usize, modulo: u128) -> Seq<u128> {
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
// TODO remove pub is just for test cases
pub fn create_invertable_poly(
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

    // lift  g in R/q (2 to q-1)
    let mut g = Seq::from_seq(&poly_g.0);
    for i in 0..n_v.p + 1 {
        if g[i] == 2{
            g[i] = n_v.q -1;
        }
    }
    //create f
    let f = create_rand_poly(n_v.w, n_v.p + 1, 3);
    // lift f in R/q (2 to q-1)
    let mut f_Rq = Seq::from_seq(&f);
    for i in 0..n_v.p + 1 {
        if f_Rq[i] == 2{
            f_Rq[i] = n_v.q -1;
        }
    }
    let f_3times = add_poly(&f_Rq, &add_poly(&f_Rq, &f_Rq, n_v.q), n_v.q);
    let mut irr: Seq<u128> = Seq::new(n_v.p + 1);
    irr[0] = n_v.q - 1;
    irr[1] = n_v.q - 1;
    irr[n_v.p] = 1 as u128;

    let f_3times_pre_inv = eea(&f_3times,&irr,n_v.q);
    let mut f_inv_3times:Seq<u128> = Seq::new(n_v.p + 1);
    match f_3times_pre_inv {
        Ok(v) => {
            f_inv_3times = v;
        }
        Err(_) => println!("Key generating, failed")
    }
    let h = mul_poly_irr(&g, &f_inv_3times, &irr,n_v.q);

    (h, (f, g_inv))
}
// IN PROGRESS (NOT WORKING)
// r is the plaintext, h is the public key
pub fn encryption(r: &Seq<u128>, h: Seq<u128>, n_v: &NtruVersion) -> Seq<u128> {
    let mut irr: Seq<u128> = Seq::new(n_v.p + 1);
    irr[0] = n_v.q - 1;
    irr[1] = n_v.q - 1;
    irr[n_v.p] = 1 as u128;
    //lift plaintext in Rq
    let mut plaintext = Seq::from_seq(r);
    for i in 0..n_v.p + 1 {
        if plaintext[i] == 2{
            plaintext[i] = n_v.q -1;
        }
    }
    round(&mul_poly_irr(&plaintext, &h, &irr, n_v.q),3)
}
// IN PROGRESS (NOT WORKING)
pub fn decryption(c: Seq<u128>, key: (Seq<u128>, Seq<u128>), n_v: &NtruVersion) -> Seq<u128> {
    let f = key.0;
    let v = key.1;

    let mut irr_3: Seq<u128> = Seq::new(n_v.p + 1);
    irr_3[0] = 2 as u128;
    irr_3[1] = 2 as u128;
    irr_3[n_v.p] = 1 as u128;

    let mut irr_q: Seq<u128> = Seq::new(n_v.p + 1);
    irr_q[0] = n_v.q -1;
    irr_q[1] = n_v.q -1;
    irr_q[n_v.p] = 1 as u128;

    //lift f from R3 to Rq
    let mut f_Rq = Seq::from(f);
    for i in 0..n_v.p + 1 {
        if f_Rq[i] == 2{
            f_Rq[i] = n_v.q -1;
        }
    }

    // calculate 3*f and 3*f*c
    let f_3 = add_poly(&f_Rq, &add_poly(&f_Rq, &f_Rq, n_v.q), n_v.q);
    let f_3_c = mul_poly_irr(&f_3, &c, &irr_q, n_v.q);

    // lift f_3_c to R_3
    let mut e = Seq::from_seq(&f_3_c);
    for i in 0..e.len(){
        if e[i] == n_v.q -1{
            e[i] = 2;
        }
        e[i] = e[i] % 3;
    }
    //identity
    let mut identity:Seq<u128> = Seq::new(n_v.p +1);
    identity[0] = 1 as u128;
    e = mul_poly_irr(&e, &identity, &irr_3, 3);
    println!("after e is {:?}",e);
    //lift to R
    mul_poly_irr(&v, &e, &irr_3,3)
}
