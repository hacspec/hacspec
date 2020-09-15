use hacspec_lib::prelude::*;

// XXX: Careful in here. The `test` functions use `Numeric` functions and hence
//      will end up being the same as what they test. Rewrite when merging!

#[test]
fn test_cswap() {
    let x = 123u8;
    let y = 234u8;

    let (xs, ys) = cswap(x, y, 0);
    assert_eq!(xs, x);
    assert_eq!(ys, y);
    let (xs, ys) = cswap_bit(x, y, 0);
    assert_eq!(xs, x);
    assert_eq!(ys, y);
    let (xs, ys) = cswap(x, y, u8::max_val());
    assert_eq!(xs, y);
    assert_eq!(ys, x);
    let (xs, ys) = cswap_bit(x, y, 1);
    assert_eq!(xs, y);
    assert_eq!(ys, x);
}

#[test]
fn test_csub() {
    fn test<T: Integer + Copy>(x: T, y: T) {
        let d = csub(x, y, T::default());
        assert!(d.equal(x));
        let d = csub(x, y, T::max_val());
        assert!(d.equal(x.wrap_sub(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_cadd() {
    fn test<T: Integer + Copy>(x: T, y: T) {
        let d = cadd(x, y, T::default());
        assert!(d.equal(x));
        let d = cadd(x, y, T::max_val());
        assert!(d.equal(x.wrap_add(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_cmul() {
    fn test<T: Integer + Copy>(x: T, y: T) {
        let d = cmul(x, y, T::default());
        assert!(d.equal(x));
        let d = cmul(x, y, T::max_val());
        assert!(d.equal(x.wrap_mul(y)));
    }
    test(13u8, 234u8);
    test(827629u64, 16u64);
}

#[test]
fn test_div() {
    fn test<T: Integer + Copy>(x: T, y: T) {
        let (q, r) = ct_div(x, y);
        assert!(q.equal(x.divide(y)));
        assert!(r.equal(x.modulo(y)));
    }

    fn test_8(x: u8, y: u8) {
        test(x, y);
        test(U8(x), U8(y));
    }
    test_8(13, 234);

    fn test_16(x: u16, y: u16) {
        test(x, y);
        test(U16(x), U16(y));
    }
    test_16(13, 234);

    fn test_32(x: u32, y: u32) {
        test(x, y);
        test(U32(x), U32(y));
    }
    test_32(827629, 12);

    fn test_64(x: u64, y: u64) {
        test(x, y);
        test(U64(x), U64(y));
    }
    test_64(827629, 12);
    test_64(16, 827629);
}

#[test]
fn test_zn_inv() {
    let n = 65537;
    // assert_eq!(u128::inv(23647, n), 52791);
    assert_eq!(u128::inv(37543865, n), 37686);
    // let n = 106103;
    // assert_eq!(u128::inv(8752725684352, n), 52673);
    // assert_eq!(u128::inv(123, n), 99202);

    // let n = 106103i128;
    // assert_eq!(i128::inv(-123, n), 6901);
}
#[test]
fn test_poly_div() {
    // x³ + 3
    let a: Seq<i128> = Seq::from_native_slice(&[3, 3]);
    // x + 1
    let b: Seq<i128> = Seq::from_native_slice(&[1, 1]);
    // 3x +3 / x + 1  (mod 4) = 3
    let mut quotient = div_poly(&a, &b, 4);
    // q = 3 and r = 0
    let r: Seq<i128> = Seq::from_native_slice(&[0, 0]);
    let q: Seq<i128> = Seq::from_native_slice(&[3, 0]);

    assert_eq!(degree_poly(&quotient.clone().unwrap().0), 0);
    assert_eq!(quotient.clone().unwrap().0[0], q[0]);
    assert_eq!(degree_poly(&quotient.clone().unwrap().1), 0);
    assert_eq!(quotient.clone().unwrap().1[0], r[0]);

    //x¹² + x
    let a_2: Seq<i128> = Seq::from_native_slice(&[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
    //x - 1
    let b_2: Seq<i128> = Seq::from_native_slice(&[-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    // (x¹² + x )/ (x-1) mod 4 = x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 2
    quotient = div_poly(&a_2, &b_2, 4);
    // q = x^11 + x^10 + x^9 + x^8 + x^7 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 2
    assert_eq!(degree_poly(&quotient.clone().unwrap().0), 11);
    for i in 1..12 {
        assert_eq!(quotient.clone().unwrap().0[i], 1i128);
    }
    assert_eq!(quotient.clone().unwrap().0[0], 2i128);
    // r = 2
    assert_eq!(degree_poly(&quotient.clone().unwrap().1), 0);
    assert_eq!(quotient.unwrap().1[0], 2i128);
}

#[test]
fn test_mul_poly() {
    //-2x + 1
    let a: Seq<i128> = Seq::from_native_slice(&[1, -2, 0, 0, 0, 0]);
    // 2x³ + x -1
    let b: Seq<i128> = Seq::from_native_slice(&[-1, 1, 0, 2, 0, 0]);
    //(-2x + 1)(2x³ + x -1) = -4 x^4 + 2 x^3 - 2 x^2 + 3 x - 1
    let product = mul_poly(&a, &b, 5);
    //-4 x^4 + 2 x^3 - 2 x^2 + 3 x - 1
    let p: Seq<i128> = Seq::from_native_slice(&[-1, 3, -2, 2, -4, 0]);
    for i in 0..6 {
        assert_eq!(product[i], p[i]);
    }
}

#[test]
fn test_mul_poly_with_unequal_sized_poly() {
    //x¹² + x
    let a: Seq<i128> = Seq::from_native_slice(&[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
    //x - 1
    let b: Seq<i128> = Seq::from_native_slice(&[-1, 1]);
    mul_poly(&a, &b, 3);
}

#[test]
fn test_poly_eea() {
    let h: Seq<i128> = Seq::from_native_slice(&[1, 0, 1, 0]);
    // x^3 + 2x + 1
    let irr: Seq<i128> = Seq::from_native_slice(&[1, 2, 0, 1]);

    let h_pre_inv = extended_euclid(&h, &irr, 3);
    let h_inv = match h_pre_inv {
        Ok(v) => v,
        Err(_) => panic!("test, failed!"),
    };
    //2x^2 -2x + 2
    let expected: Seq<i128> = Seq::from_native_slice(&[2, 1, 2]);
    assert_eq!(h_inv.len(), expected.len());
    for i in 0..h_inv.len() {
        assert_eq!(h_inv[i], expected[i]);
    }
    let scalar = mul_poly_irr(&h, &h_inv, &irr, 3);
    let one: Seq<i128> = Seq::from_native_slice(&[1, 0, 0, 0]);
    assert_eq!(scalar.len(), one.len());
    for i in 0..scalar.len() {
        assert_eq!(one[i], scalar[i]);
    }
}
