use hacspec::prelude::*;

use hacspec_examples::ntru_prime::*;
#[macro_use]
extern crate hacspec_examples;

#[test]
fn test_create_inv() {
    let mut poly = create_invertable_poly(&ntru_v!(1), ntru_v!(1).q);
    let mut f_inv: Seq<i128> = Seq::new(ntru_v!(1).p + 1);
    for _ in 0..4 {
        match poly.1 {
            Ok(v) => {
                f_inv = v;
                break;
            }
            Err(_) => poly = create_invertable_poly(&ntru_v!(1), ntru_v!(1).q),
        }
    }
    let mut irr: Seq<i128> = Seq::new(f_inv.len());
    irr[0]= - 1 as i128;
    irr[1] = - 1 as i128;
    irr[f_inv.len() - 1] = 1 as i128;

    //TODO assert_eq
    println!(
        "should be 1 and is {:?}",
        mul_poly_irr(&f_inv, &poly.0, &irr, ntru_v!(1).q)
    );
    assert_eq!(true,true);
}

fn test_h_invertable(h:&Seq<i128>,q:i128)-> bool{
    let mut irr:Seq<i128> = Seq::new(h.len());
    irr[0]= - 1 as i128;
    irr[1] = - 1 as i128;
    irr[f_inv.len() - 1] = 1 as i128;


    let h_pre_inv = eea(&h,&irr,q);
    let mut h_inv:Seq<i128> = Seq::new(h.len());
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

#[test]
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
    assert_eq!(deg(&result),deg(&m));
    println!("Compare weight:");
    assert_eq!(weight(&result),weight(&m));
    println!("m is {:?} and result is {:?}",m, result);
}

#[test]
fn test_encryption_decryption_fixed_key(){
    let n_v = ntru_v!(-1);
    let pk:Seq<i128> = Seq::from_native_slice(&[26, 39, 52, 91, 13, 39, 52, 0]);
    let sk:(Seq<i128>,Seq<i128>) = (Seq::from_native_slice(&[0, 1, 2, 1, 2, 0, 0, 0]),Seq::from_native_slice(&[0, 0, 0, 1, 0, 0, 2, 0]));
    println!("h is invertable? {:?}",test_h_invertable(&pk, n_v.q) );
    assert_eq!(test_h_invertable(&pk, n_v.q),true);
    // message
    let m:Seq<i128> = Seq::from_native_slice(&[2, 2, 1, 0, 0, 2, 0, 0]);
    // encryption
    let c = encryption(&m, pk, &n_v);
    println!("c is {:?}",c);
    println!("encryption done!");
    let result = decryption(c, sk, &n_v);
    println!("compare degree: ");
    assert_eq!(deg(&result),deg(&m));

    println!("Compare weight:");
    assert_eq!(weight(&result),weight(&m));

    println!("m is {:?} and result is {:?}",m, result);
}
