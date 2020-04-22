use hacspec::prelude::*;

use crate::ntru::*;


#[test]
fn test_key_gen(){
    key_gen();
    //assert_eq!(p,5);
    //assert_eq!(g,g_inv);
}
#[test]
fn test_create_inv(){
    let mut poly = create_invertable_poly_2( NtruVersion{p:653,q:4621,w:288},3);
    while poly.1.len() == 0 {
        poly = create_invertable_poly_2( NtruVersion{p:653,q:4621,w:288}, 3);
    }
    // convert vec to array
    let mut f_array:[u128;653] = [0;653];
    let mut index = 0;
    while index < 653{
            f_array[index] = poly.1[index];
            index = index + 1;
    }
    
    poly!(ZxQ, u128, 653, 3, [(0, 2), (1, 2), (653, 1)]);
    let f_inv = ZxQ::new_full(f_array);
    let f = ZxQ::new(&poly.0);
    let result = ZxQ::new(&[(0,1)]);
    assert_eq!(result,f.mul(f_inv) );
}