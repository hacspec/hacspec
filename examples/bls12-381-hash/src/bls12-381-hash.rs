use hacspec_lib::*;
use hacspec_bls12_381::*;
use hacspec_sha256::*;


public_nat_mod!( //Need a bigger canvas to do a random 512 bit number modulo p
    type_name: FpHash,
    type_of_canvas: FpHashCanvas,
    bit_size_of_field: 512, 
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

bytes!(Dst, 27);
array!(ArrFp, 6, U64);

const B_IN_BYTES : usize = 32;
const S_IN_BYTES : usize = 64;
const L : usize = 64;

//hacspec_v0.1.0_BLS12_381_G1
const G1_DST : Dst = Dst(secret_bytes!([
    0x68u8, 0x61u8, 0x63u8, 0x73u8, 0x70u8, 0x65u8, 0x63u8, 0x5fu8, 0x76u8, 0x30u8, 0x2eu8, 0x31u8, 0x2eu8, 0x30u8, 0x5fu8, 0x42u8, 
    0x4cu8, 0x53u8, 0x31u8, 0x32u8, 0x5fu8, 0x33u8, 0x38u8, 0x31u8, 0x5fu8, 0x47u8, 0x31u8]));

//hacspec_v0.1.0_BLS12_381_G2
const G2_DST : Dst = Dst(secret_bytes!([
    0x68u8, 0x61u8, 0x63u8, 0x73u8, 0x70u8, 0x65u8, 0x63u8, 0x5fu8, 0x76u8, 0x30u8, 0x2eu8, 0x31u8, 0x2eu8, 0x30u8, 0x5fu8, 0x42u8, 
    0x4cu8, 0x53u8, 0x31u8, 0x32u8, 0x5fu8, 0x33u8, 0x38u8, 0x31u8, 0x5fu8, 0x47u8, 0x32u8]));

//(p - 1) / 2 
// 0d0088f51cbff34d 258dd3db21a5d66b b23ba5c279c2895f b39869507b587b12 0f55ffff58a9ffff dcff7fffffffd555
const P_1_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0d0088f51cbff34du64, 0x258dd3db21a5d66bu64, 0xb23ba5c279c2895fu64,
        0xb39869507b587b12u64, 0x0f55ffff58a9ffffu64, 0xdcff7fffffffd555u64
    ]
));

//(p + 1) / 4
// 0680447a8e5ff9a6 92c6e9ed90d2eb35 d91dd2e13ce144af d9cc34a83dac3d89 07aaffffac54ffff ee7fbfffffffeaab
const P_1_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64, 0x92c6e9ed90d2eb35u64, 0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64, 0x07aaffffac54ffffu64, 0xee7fbfffffffeaabu64
    ]
));

//(p - 3) / 4
// 0680447a8e5ff9a6 92c6e9ed90d2eb35 d91dd2e13ce144af d9cc34a83dac3d89 07aaffffac54ffff ee7fbfffffffeaaa
const P_3_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64, 0x92c6e9ed90d2eb35u64, 0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64, 0x07aaffffac54ffffu64, 0xee7fbfffffffeaaau64
    ]
));

pub fn expand_message_xmd(msg: &ByteSeq, dst: &ByteSeq, len_in_bytes: usize) -> ByteSeq {
    let ell = (len_in_bytes + B_IN_BYTES - 1) / B_IN_BYTES;
    // must be that ell <= 255
    let dst_prime = dst.push(&U8_from_usize(dst.len()));
    let z_pad = ByteSeq::new(S_IN_BYTES);
    let l_i_b_str = ByteSeq::new(0).push(&U8_from_usize(len_in_bytes/256)).push(&U8_from_usize(len_in_bytes)); 
    let msg_prime = z_pad.concat(msg).concat(&l_i_b_str).concat(&ByteSeq::new(1)).concat(&dst_prime); // Z_pad || msg || l_i_b_str || 0 || dst_prime
    let b_0 = ByteSeq::from_seq(&hash(&msg_prime)); // H(msg_prime)
    let mut b_i =  ByteSeq::from_seq(&hash(&b_0.push(&U8(1u8)).concat(&dst_prime))); // H(b_0 || 1 || dst_prime)
    let mut uniform_bytes = ByteSeq::from_seq(&b_i);
    for _ in 2..(ell + 1) {
        let t = ByteSeq::from_seq(&b_0);
        b_i = ByteSeq::from_seq(&hash(&(t ^ b_i).push(&U8(1u8)).concat(&dst_prime))); //H((b_0 ^ b_(i-1)) || 1 || dst_prime)
        uniform_bytes = uniform_bytes.concat(&b_i);
    }
    uniform_bytes.truncate(len_in_bytes)
}

pub fn fp_hash_to_field(msg: &ByteSeq, count: usize) -> Seq<Fp> {
    let len_in_bytes = count * L; // count * m * L
    let dst = ByteSeq::from_seq(&G1_DST); 
    let uniform_bytes = expand_message_xmd(msg, &dst, len_in_bytes);
    let mut output = Seq::<Fp>::new(0);
    for i in 0..count {
        // m = 1, so no loop
        let elm_offset = L * i; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let u_i = Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output = output.push(&u_i);
    } 
    output
}

//Returns true if x is odd and false otherwise
fn fp_sgn0(x: Fp) -> bool {
    x % Fp::TWO() == Fp::ONE()
}

fn fp_is_square(x: Fp) -> bool {
    let c1 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let tv = x.pow_self(c1);       
    tv == Fp::ZERO() || tv == Fp::ONE()
}

fn fp_sqrt(x: Fp) -> Fp {
    let c1 = Fp::from_byte_seq_be(&P_1_4.to_be_bytes()); // (p + 1) / 4
    x.pow_self(c1)
}

// y^2 = g(x) = x^3 + 4
fn g1_curve_func(x: Fp) -> Fp { 
    x * x * x + Fp::from_literal(4u128)
}

fn g1_map_to_curve(u: Fp) -> G1 {
    let z = Fp::ZERO() - Fp::from_literal(3u128); 
    let gz = g1_curve_func(z);
    let tv1 = u * u * gz;
    let tv2 = Fp::ONE() + tv1;
    let tv1 = Fp::ONE() - tv1;
    let tv3 = (tv1 * tv2).inv();
    let mut tv4 = fp_sqrt((Fp::ZERO() - gz) * (Fp::from_literal(3u128) * z * z)); // sqrt(-g(Z) * (3 * Z^2 + 4 * A))
    if fp_sgn0(tv4) {
        tv4 = Fp::ZERO() - tv4;
    }
    let tv5 = u * tv1 * tv3 * tv4;
    let tv6 = (Fp::ZERO() - Fp::from_literal(4u128)) * gz * (Fp::from_literal(3u128) * z * z).inv(); // -4 * g(Z) / (3 * Z^2 + 4 * A) 
    let x1 = (Fp::ZERO() - z) * Fp::TWO().inv() - tv5;
    let x2 = (Fp::ZERO() - z) * Fp::TWO().inv() + tv5;
    let x3 = z + tv6 * (tv2 * tv2 * tv3) * (tv2 * tv2 * tv3);
    let x = if fp_is_square(g1_curve_func(x1)) {
        x1
    } else { if fp_is_square(g1_curve_func(x2)) {
        x2
    } else {
        x3
    }};
    let mut y = fp_sqrt(g1_curve_func(x));
    if fp_sgn0(u) != fp_sgn0(y) {
        y = Fp::ZERO() - y;
    }
    (x, y, false)
}


fn g1_clear_cofactor(x: G1) -> G1 {
    let h_eff = Scalar::from_literal(0xd201000000010001u128);
    g1mul(h_eff, x)
}

pub fn g1_hash_to_curve(msg: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, 2);
    let q0 = g1_map_to_curve(u[0]);
    let q1 = g1_map_to_curve(u[1]); 
    let r = g1add(q0, q1);
    let p = g1_clear_cofactor(r);
    p
}

pub fn fp2_hash_to_field(msg: &ByteSeq, count: usize) -> Seq<Fp2> {
    let len_in_bytes = count * 2 * L; // count * m * L
    let dst = ByteSeq::from_seq(&G2_DST); // not hacspec
    let uniform_bytes = expand_message_xmd(msg, &dst, len_in_bytes);
    let mut output = Seq::<Fp2>::new(0);
    for i in 0..count {
        // m = 2
        let elm_offset = L * i * 2; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_1 = Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p

        let elm_offset = L * (1 + i * 2); // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_2 = Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output = output.push(&(e_1, e_2));
    } 
    output
}

pub fn fp2_sgn0(x: Fp2) -> bool {
    let (x0, x1) = x;
    let sign_0 = fp_sgn0(x0);
    let zero_0 = x0 == Fp::ZERO();
    let sign_1 = fp_sgn0(x1);
    sign_0 || (zero_0 && sign_1)
}

pub fn fp2_is_square(x: Fp2) -> bool {
    let c1 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let (x1, x2) = x;
    let tv1 = x1 * x1;
    let tv2 = x2 * x2;
    let tv1 = tv1 + tv2;
    let tv1 = tv1.pow_self(c1);
    let neg1 = Fp::ZERO() - Fp::ONE();
    tv1 != neg1
}

fn fp2exp(n: Fp2, k: Fp) -> Fp2 {
    let mut c = fp2fromfp(Fp::ONE());
    for i in 0..381 {
        //starting from second most significant bit
        c = fp2mul(c, c);
        if k.bit(380 - i) {
            c = fp2mul(c, n);
        }
    }
    c
}

// Algorithm 9 from https://eprint.iacr.org/2012/685.pdf
pub fn fp2_sqrt(a: Fp2) -> Fp2 {
    let c1 = Fp::from_byte_seq_be(&P_3_4.to_be_bytes()); // (p - 3) / 4
    let c2 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let a1 = fp2exp(a, c1); // a ^ ((q-3)/4)
    let alpha = fp2mul(a1, fp2mul(a1, a)); // a1(a1(a))
    //let a0 = fp2mul(fp2conjugate(alpha), alpha); //alpha^q * alpha
    let x0 = fp2mul(a1, a); //a1 * a
    let neg1 = (Fp::ZERO() - Fp::ONE(), Fp::ZERO());
    let b = fp2exp(fp2add(fp2fromfp(Fp::ONE()), alpha), c2); // (1 + alpha) ^ ((q-1)/2)
    if alpha == neg1 {
        fp2mul((Fp::ZERO(), Fp::ONE()), x0) // i * x0
    } else {
        
        fp2mul(b, x0) // b * x0
    }
}

pub fn g2_curve_func(x: Fp2) -> Fp2 {
    fp2add(fp2mul(x, fp2mul(x, x)), (Fp::from_literal(4u128), Fp::from_literal(4u128)))
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod test {
    use super::*;


    #[test]
    fn test_fp_sgn0() {
        let a = Fp::from_hex("243171");
        assert!(fp_sgn0(a));
        let b = Fp::from_hex("2431710293859032");
        assert!(!fp_sgn0(b));
    }

    #[test]
    fn test_fp2_sgn0() {
        let a = Fp::from_hex("24e31f71");
        let b = Fp::from_hex("243d17ee10293859032");
        assert!(fp2_sgn0((a, b)));
        let z = Fp::ZERO();
        let c = Fp::from_hex("598325bc69");
        assert!(fp2_sgn0((z, c)));
        let d = Fp::from_hex("9879a032b6");
        assert!(!fp2_sgn0((z, d)));
    }

    #[test]
    fn test_fp_square() {
        let x = Fp::from_literal(4);
        assert!(fp_is_square(x));
    }

    #[test]
    fn test_fp_sqrt() {
        let x = Fp::from_literal(256);
        let k = fp_sqrt(x);
        assert_eq!(k*k, x);
    }

    #[test]
    fn test_fp2_is_square() {
        let x = (Fp::from_literal(54), Fp::from_literal(34));
        let y = fp2mul(x, x);
        assert!(fp2_is_square(y));
        assert!(!fp2_is_square(x));
    }

    #[test]
    fn test_fp2_sqrt() {
        let x = (Fp::ZERO() - Fp::from_literal(54), Fp::from_literal(34));
        let y = fp2mul(x, x);
        let k = fp2_sqrt(y);
        assert_eq!(fp2mul(k,k), y);

    }

    #[test]
    fn test_g1_map_to_curve() {
        let u = Fp::from_literal(3082);
        let (x, y, _) = g1_map_to_curve(u);
        assert_eq!(y*y, x*x*x + Fp::from_literal(4));
    }

    #[quickcheck]
    fn test_prop_g1_map_to_curve(a : u128) -> bool {
        let u = Fp::from_literal(a);
        let (x, y, _) = g1_map_to_curve(u);
        y*y == x*x*x + Fp::from_literal(4)
    }

    #[test]
    fn test_fp_correct_z() {
        let z = Fp::ZERO() - Fp::from_literal(3);
        let gz = g1_curve_func(z);
        assert!(gz != Fp::ZERO());
        let t = (Fp::ZERO() - (Fp::from_literal(3) * z*z)) / (Fp::from_literal(4) * gz);
        assert!(t != Fp::ZERO());
        assert!(fp_is_square(t));
        assert!(fp_is_square(gz) || fp_is_square(g1_curve_func((Fp::ZERO() - z) / Fp::TWO() )));
    }

    #[test]
    fn test_g1_hash_to_curve() {
        let msg1 = ByteSeq::from_public_slice(b"hello world");
        let p1 = g1_hash_to_curve(&msg1);
        let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
        let h = g1mul(r, p1);
        assert!(h.2); // in the correct sub-group
        let msg2 = ByteSeq::from_public_slice(b"hello world");
        let p2 = g1_hash_to_curve(&msg2);
        assert_eq!(p1, p2); // deterministic
        let msg3 = ByteSeq::from_public_slice(b"hello world2");
        let p3 = g1_hash_to_curve(&msg3);
        assert!(p1 != p3); // not trivial
    }

    #[test]
    fn test_fp2_correct_z() {
        let z = fp2fromfp(Fp::ZERO() - Fp::ONE());
        let gz = g2_curve_func(z);
        assert!(gz != fp2zero());
        let t = fp2mul(fp2neg(fp2mul(fp2fromfp(Fp::from_literal(3)), fp2mul(z, z))), fp2inv(fp2mul(fp2fromfp(Fp::from_literal(4)), gz)));
        //let t = (Fp::ZERO() - (Fp::from_literal(3) * z*z)) / (Fp::from_literal(4) * gz);
        assert!(t != fp2zero());
        assert!(fp2_is_square(t));
        assert!(fp2_is_square(gz));
        // || fp_is_square(g1_curve_func((Fp::ZERO() - z) / Fp::TWO() ))
    }

    #[test]
    fn test_1() {
        let c1 = Fp::from_hex("d0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd555"); // (p - 1) / 2
        let c2 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes());
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_2() {
        let u = Fp::from_literal(5);
        let (x, y, _) = g1_map_to_curve(u);
        assert_eq!((x, y, false), (Fp::ZERO(), Fp::ZERO(), true));
    }


}
