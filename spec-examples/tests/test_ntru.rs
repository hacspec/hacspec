use hacspec::prelude::*;

use hacspec_examples::ntru_prime::*;
/*
#[test]
fn test_key_gen(){
    ntru_prime::key_gen();
    //assert_eq!(p,5);
    //assert_eq!(g,g_inv);
}*/
#[test]
fn test_create_inv(){
    let mut poly = create_invertable_poly(&ntru_v!(1), ntru_v!(1).q);
    let mut f_inv: Seq<u128> = Seq::new(ntru_v!(1).p + 1);
    for _ in 0..4 {
        match poly.1 {
            Ok(v) => {
                f_inv = v;
                break;
            }
            Err(_) => poly = create_invertable_poly(&ntru_v!(1), ntru_v!(1).q),
        }
    }
    let mut irr: Seq<u128> = Seq::new(f_inv.len());
    irr[0] = ntru_v!(1).q -1;
    irr[1] = ntru_v!(1).q -1;
    irr[f_inv.len() - 1] = 1 as u128;

    //TODO assert_eq 
    println!(
        "should be 1 and is {:?}",
        mul_poly_irr(&f_inv, &poly.0, &irr, ntru_v!(1).q)
    );
}
