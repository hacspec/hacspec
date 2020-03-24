use hacspec::prelude::*;

#[test]
fn test_zn_inv() {
    let n = 65537;
    assert_eq!(u128::invert(23647, n), 52791);
    assert_eq!(u128::invert(37543865, n), 37686);
    let n = 106103;
    assert_eq!(u128::invert(8752725684352, n), 52673);
    assert_eq!(u128::invert(123, n), 99202);

    let n = 106103i128;
    assert_eq!(i128::invert(-123, n), 6901);
}

#[test]
fn test_poly_add() {
    // Polynomials without irreducible and without coefficient modulus.
    poly!(Zx, u128, 256, 0, &[(0, 0)]);
    poly!(Zs, i128, 256, 0, &[(0, 0)]);

    let a = Zx::new(&[(78, 1), (222, 1)]);
    let b = Zx::new(&[(0, 1), (222, 2)]);
    let e = Zx::new(&[(0, 1), (78, 1), (222, 3)]);
    let c = a + b;
    println!("{:x?} + {:x?} = {:x?}\nexpected: {:x?}", a, b, c, e);
    assert_eq!(c, e);

    let a = Zs::new(&[(0, -1), (78, 1)]);
    let b = Zs::new(&[(0, 1), (78, 0), (222, -5)]);
    let e = Zs::new(&[(78, 1), (222, -5)]);
    let c = a + b;
    println!("{:x?} + {:x?} = {:x?}\nexpected: {:x?}", a, b, c, e);
    assert_eq!(c, e);

    // Polynomials without irreducible but with coefficient modulus.
    poly!(ZxN, u128, 256, 3, &[(0, 0)]);
    poly!(ZsN, i128, 256, 3, &[(0, 0)]);

    let a = ZxN::new(&[(78, 1), (222, 1)]);
    let b = ZxN::new(&[(0, 1), (222, 2)]);
    let e = ZxN::new(&[(0, 1), (78, 1)]);
    let c = a + b;
    println!("{:x?} + {:x?} = {:x?}\nexpected: {:x?}", a, b, c, e);
    assert_eq!(c, e);

    let a = ZsN::new(&[(0, -1), (78, 1)]);
    let b = ZsN::new(&[(0, 1), (222, -5)]);
    let e = ZsN::new(&[(78, 1), (222, 1)]);
    let c = a + b;
    println!("{:x?} + {:x?} = {:x?}\nexpected: {:x?}", a, b, c, e);
    assert_eq!(c, e);
}

// #[test]
// fn test_poly_sub() {
// }

#[test]
fn test_poly_div() {
    const L: usize = 3;
    poly!(ZxN, u128, L, 3, &[(0, 2), (1, 2), (3, 1)]);
    poly!(ZsN, i128, L, 3, &[(0, 2), (1, 2), (3, 1)]);

    let x = ZxN::new(&[(0, 1), (2, 2)]);
    let y = ZxN::new(&[(1, 1), (2, 1)]);
    let expected_c = ZxN::new(&[(0, 2)]);
    let expected_r = ZxN::new(&[(0, 1), (1, 1)]);

    let (c, r) = x / y;
    println!("{:x?} / {:x?} = {:x?}, {:x?}", x, y, c, r);
    assert_eq!(c, expected_c);
    assert_eq!(r, expected_r);

    let x = ZsN::new(&[(0, 1), (2, 2)]);
    let y = ZsN::new(&[(1, 1), (2, 1)]);
    let expected_c = ZsN::new(&[(0, 2)]);
    let expected_r = ZsN::new(&[(0, 1), (1, 1)]);

    let (c, r) = x / y;
    println!("{:x?} / {:x?} = {:x?}, {:x?}", x, y, c, r);
    assert_eq!(c, expected_c);
    assert_eq!(r, expected_r);
}

#[test]
fn test_poly_mul() {
    const L: usize = 3;
    poly!(ZxN, u128, L, 11, &[(0, 2), (1, 2), (3, 1)]);
    poly!(ZsN, i128, L, 11, &[(0, 2), (1, 2), (3, 1)]);

    let x = ZxN::new(&[(0, 1), (2, 2)]);
    let y = ZxN::new(&[(1, 1), (2, 1)]);
    let expected = ZxN::new(&[(0, 7), (1, 4), (2, 8)]);

    let c = x * y;
    println!("{:x?} * {:x?} = {:x?}", x, y, c);
    assert_eq!(c, expected);

    let x = ZsN::new(&[(0, 1), (2, 2)]);
    let y = ZsN::new(&[(1, 1), (2, 1)]);
    let expected = ZsN::new(&[(0, 7), (1, 4), (2, 8)]);

    let c = x * y;
    println!("{:x?} * {:x?} = {:x?}", x, y, c);
    assert_eq!(c, expected);

    let x = ZsN::new(&[(0, -3), (1, 5), (2, -1)]);
    let y = ZsN::new(&[(0, 1), (1, -2), (2, -7)]);
    let expected = ZsN::new(&[(0, 8), (1, 8), (2, 7)]);

    let c = x * y;
    println!("{:x?} * {:x?} = {:x?}", x, y, c);
    assert_eq!(c, expected);

    // Use random values, so no expected value possible here.
    poly!(ZxLarge, u128, 592_358, 86_028_121, &[(0, 2), (1, 2), (3, 1)]);
    let a = ZxN::random();
    let b = ZxN::random();
    let r = a * b;
    println!("{:x?} * {:x?} = {:x?}", a, b, r);
}

#[test]
fn test_poly_inversion() {
    const L: usize = 3;
    poly!(ZxN, u128, L, 3, &[(0, 2), (1, 2), (3, 1)]);
    // TODO: Signed inversion?
    let one_poly = ZxN::new(&[(0, 1)]);

    let a = ZxN::new(&[(0, 2), (1, 2)]);
    let a_inv = a.inv();
    let test = a * a_inv;
    assert_eq!(test, one_poly);
    
    let a = ZxN::new(&[(0, 1), (1, 2), (2, 2)]);
    let a_inv = a.inv();
    let test = a * a_inv;
    assert_eq!(test, one_poly);
    
    let a = ZxN::new(&[(2, 1)]);
    let a_inv = a.inv();
    let test = a * a_inv;
    assert_eq!(test, one_poly);
}

#[test]
#[should_panic]
fn test_poly_inversion_panic() {
    poly!(ZxN, u128, 11, 3, &[(0, 2), (1, 2), (2, 1), (3, 2), (4, 2), (5, 1), (6, 2), (8, 2), (10, 2), (11, 2)]);
    // Not invertible
    // let irr = [2, 2, 1, 2, 2, 1, 2, 0, 2, 0, 2, 2];
    let a = ZxN::new_full([0, 1, 2, 0, 2, 2, 0, 0, 2, 0, 0]);
    let _ = a.inv();
}

// Rq = Z[X]/(3329, (X^256+1))
poly!(RqKyberFixedLength, u128, 256, 3329, &[(0, 1), (256, 1)]);

#[test]
fn test_fixed_length() {
    let a = RqKyberFixedLength::new(&[(0, 1), (5, 55), (77, 123)]);
    let b = RqKyberFixedLength::random();
    let c = a * b;
    println!("{:x?} * {:x?} = {:x?}", a, b, c);

    let b = RqKyberFixedLength::new_full([0x72a, 0x50b, 0x6db, 0x26e, 0x536, 0x253, 0x292, 0x42f, 0x2da, 0x92b, 0x9b4, 0xbfc, 0x263, 0x636, 0x78b, 0x82e, 0x54a, 0x8cf, 0xc3, 0xa30, 0x99e, 0x2f4, 0x696, 0x2be, 0x2a6, 0x159, 0x147, 0x4b, 0xa44, 0x255, 0x9c5, 0x1a7, 0xa61, 0x640, 0xca3, 0xb51, 0x761, 0xbf2, 0x210, 0x25e, 0xa90, 0x25b, 0x1ab, 0x5e5, 0x7a2, 0x235, 0x9d0, 0x373, 0x55, 0xc46, 0x1c3, 0x90a, 0x21b, 0xa0d, 0x73e, 0x6ce, 0x4b4, 0x355, 0x681, 0x667, 0x8a0, 0x3e, 0xb79, 0x190, 0xbab, 0x137, 0xb43, 0x493, 0x399, 0x8e8, 0x731, 0x24b, 0x43f, 0x9ef, 0x206, 0x5d4, 0x252, 0x9da, 0x449, 0xa34, 0xc13, 0x5c2, 0x6f, 0x1d1, 0x397, 0x6f7, 0xc9c, 0x736, 0x95a, 0x6ef, 0x724, 0x25b, 0xcec, 0x784, 0xab5, 0xbc2, 0x12f, 0x5ff, 0x834, 0x34e, 0x282, 0x47d, 0x874, 0x46e, 0xced, 0x682, 0x329, 0x5ab, 0x7ca, 0x3df, 0xcd6, 0x412, 0x444, 0xa7e, 0xc61, 0x9b1, 0xa59, 0x612, 0x2bc, 0x391, 0xd, 0xa48, 0x46c, 0xa9a, 0xc7b, 0x4a4, 0x873, 0xc48, 0x114, 0x8a6, 0x666, 0xad9, 0x5ce, 0x13f, 0x88d, 0x4c3, 0xae6, 0x9fe, 0x548, 0x8f8, 0x422, 0x653, 0x67a, 0x39a, 0x57e, 0xa95, 0x33, 0x76d, 0x101, 0xc89, 0xbd, 0x8b0, 0x146, 0x916, 0x5d, 0x577, 0x278, 0x16a, 0x6e, 0x558, 0xc59, 0xce4, 0x7f0, 0xbe5, 0x6c7, 0x84b, 0xac4, 0x8c1, 0x5b5, 0xd7, 0x993, 0x207, 0xb74, 0xf1, 0x926, 0x75c, 0x8c3, 0x1c4, 0x86d, 0x9ee, 0x380, 0x32a, 0x8dd, 0x56, 0x747, 0x20c, 0x737, 0x596, 0x292, 0x811, 0x4a8, 0x4f2, 0xb45, 0x158, 0x226, 0xc72, 0x99a, 0x1cd, 0x520, 0x6b1, 0x250, 0xbbb, 0x140, 0x476, 0x5e8, 0x45, 0x3a, 0x708, 0x3f1, 0x32a, 0xa6a, 0x694, 0x2f4, 0x39e, 0x5ad, 0xb2b, 0x7e1, 0xb5c, 0xe1, 0xc64, 0x1f3, 0x90b, 0x67a, 0x66c, 0x478, 0x647, 0x227, 0x26, 0x912, 0x581, 0x666, 0x884, 0x879, 0x30c, 0x142, 0x8c5, 0x72d, 0x3da, 0x48a, 0x15b, 0xca0, 0x284, 0x4e7, 0x6cc, 0x7ad, 0x29b, 0x3be, 0x63f, 0x655, 0x22a, 0x12f, 0x32b, 0x898, 0xaa1, 0xc3, 0x9fc]);
    let c = a * b;
    let expected_c = RqKyberFixedLength::new_full([766, 3113, 2145, 433, 3310, 2147, 553, 246, 2197, 1441, 928, 2499, 339, 3140, 2150, 1155, 1259, 3175, 981, 701, 145, 2410, 2688, 2028, 323, 3043, 130, 2446, 2933, 334, 1742, 87, 2719, 3217, 2068, 1681, 3068, 972, 493, 1051, 1584, 3173, 387, 3052, 2851, 1915, 1137, 3201, 1839, 1443, 1366, 2251, 678, 123, 2157, 257, 2144, 958, 1928, 631, 2073, 1646, 601, 861, 2285, 3229, 819, 1595, 2681, 472, 739, 2039, 2358, 2312, 962, 2195, 1456, 1595, 145, 621, 1865, 1815, 2279, 1916, 5, 1916, 131, 557, 2524, 971, 2511, 2860, 2868, 526, 1554, 1033, 1378, 267, 1168, 2776, 2863, 1338, 2522, 392, 2471, 688, 946, 1982, 3207, 460, 2093, 685, 1129, 1816, 1038, 1809, 1337, 1384, 2885, 1357, 2491, 2505, 2963, 645, 2227, 2371, 749, 1033, 1398, 1219, 622, 239, 2508, 470, 2506, 3152, 919, 2998, 3220, 1237, 788, 3146, 835, 450, 2070, 1074, 17, 3279, 3324, 1184, 2571, 2163, 2103, 2969, 760, 249, 1471, 2334, 3074, 162, 812, 1292, 1563, 1, 1094, 1051, 3101, 2616, 88, 3174, 2994, 3208, 396, 1350, 3232, 2167, 1686, 990, 276, 1373, 981, 1871, 2346, 1843, 562, 2114, 1840, 1092, 394, 2487, 858, 3275, 534, 2829, 2328, 1712, 1292, 943, 1081, 1420, 307, 1867, 2020, 3122, 3063, 3326, 1446, 1160, 2581, 428, 2421, 1143, 18, 111, 1105, 2859, 868, 1514, 617, 727, 1501, 3223, 2113, 318, 3289, 741, 3259, 1289, 104, 1228, 3273, 647, 3228, 3157, 2499, 2666, 378, 3076, 547, 1673, 1892, 2158, 359, 1829, 412, 1927, 2901, 2578, 1366, 3205, 51, 2009, 2293, 1575, 3036, 1567]);
    println!("{:x?} * {:x?} = {:x?}", a, b, c);
    assert_eq!(c, expected_c);
}
