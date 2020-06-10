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
fn create_rand_poly(w: u128, h_deg: usize, modulo: u128) -> Seq<u128> {
    let mut counter: usize = 0;
    let mut pos;
    let mut polynom: Seq<u128> = Seq::new(h_deg);

    for _ in 0..h_deg * h_deg * h_deg * h_deg *h_deg *h_deg {
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
    let f: Seq<u128> = create_rand_poly(n.w, n.p + 1, modulus);
    let mut irr: Seq<u128> = Seq::new(n.p + 1);
    irr[0] = modulus - 1;
    irr[1] = modulus - 1;
    irr[n.p] = 1 as u128;
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

// r is the plaintext, h is the public key
fn encryption(r: &Seq<u128>, h: Seq<u128>, n_v: &NtruVersion) -> Seq<u128> {
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
    println!("plaintext {:?}",plaintext);
    round(&mul_poly_irr(&plaintext, &h, &irr, n_v.q),3)
}

fn decryption(c: Seq<u128>, key: (Seq<u128>, Seq<u128>), n_v: &NtruVersion) -> Seq<u128> {
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
    println!(" pre e is {:?}",e);
    //identity
    let mut identity:Seq<u128> = Seq::new(n_v.p +1);
    identity[0] = 1 as u128;
    e = mul_poly_irr(&e, &identity, &irr_3, 3);
    println!("after e is {:?}",e);
    //lift to R
    mul_poly_irr(&v, &e, &irr_3,3)
}

fn test_encryption_decryption() {
    let n_v = ntru_v!(-1);
    let keys = key_gen(&n_v);
    println!("{:?}",keys);
    let pk = keys.0;
    let sk = keys.1;

    // message
    let m = create_rand_poly(n_v.w,n_v.p + 1 ,3);
    // encryption
    let c = encryption(&m, pk, &n_v);
    println!("encryption done!");
    println!("c is {:?}", c);
    let result = decryption(c, sk, &n_v);
    //assert_eq!(deg(&result),deg(&m));
    println!("Compare weight:");
    //assert_eq!(weight(&result),weight(&m));
    println!("m is {:?} and result is {:?}",m, result);
}
fn test_key_gen(){
    let key = key_gen(&ntru_v!(1));
    assert_eq!(leading_coef(&(key.1).0),leading_coef(&(key.1).1));
}

fn test_encryption_decryption_2(){
    let n_v = ntru_v!(-1);
    let pk:Seq<u128> = Seq::from_native_slice(&[26, 39, 52, 91, 13, 39, 52, 0]);
    let sk:(Seq<u128>,Seq<u128>) = (Seq::from_native_slice(&[0, 1, 2, 1, 2, 0, 0, 0]),Seq::from_native_slice(&[0, 0, 0, 1, 0, 0, 2, 0]));
    println!("h is invertable? {:?}",test_h_invertable(&pk, n_v.q) );
    assert_eq!(test_h_invertable(&pk, n_v.q),true);
    // message
    let m:Seq<u128> = Seq::from_native_slice(&[2, 2, 1, 0, 0, 2, 0, 0]);
    // encryption
    let c = encryption(&m, pk, &n_v);
    println!("c is {:?}",c);
    println!("encryption done!");
    let result = decryption(c, sk, &n_v);
    //assert_eq!(deg(&result),deg(&m));

    println!("Compare weight:");
    //assert_eq!(weight(&result),weight(&m));

    println!("m is {:?} and result is {:?}",m, result);
}

fn test_h_invertable(h:&Seq<u128>,q:u128)-> bool{
    let mut irr:Seq<u128> = Seq::new(h.len());
    irr[0] = q-1;
    irr[1] = q-1;
    irr[h.len() -1] = 1 as u128;


    let h_pre_inv = eea(&h,&irr,q);
    let mut h_inv:Seq<u128> = Seq::new(h.len());
    match h_pre_inv {
        Ok(v) => {
            h_inv = v;
        }
        Err(_) => println!("Key generating, failed")
    }
    if deg(&h_inv) != 0{
        return true;
    }
    return false;
    }



fn main() {
    //test_encryption_decryption();
    test_encryption_decryption_2();
}
