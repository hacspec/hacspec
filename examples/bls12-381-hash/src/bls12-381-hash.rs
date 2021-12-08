/* Hashing to Elliptic Curves: https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html
For the BLS12-381 curve.  */

use hacspec_bls12_381::*;
use hacspec_lib::*;
use hacspec_sha256::*;

public_nat_mod!( //Need a bigger canvas than the 384 bits from the Fp natmod from bls12-381 to do a random 512 bit number modulo p
    type_name: FpHash,
    type_of_canvas: FpHashCanvas,
    bit_size_of_field: 512,
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"
);

array!(ArrFp, 6, U64);

const B_IN_BYTES: usize = 32;
const S_IN_BYTES: usize = 64;
const L: usize = 64;

//(p - 1) / 2 : 0d0088f51cbff34d 258dd3db21a5d66b b23ba5c279c2895f b39869507b587b12 0f55ffff58a9ffff dcff7fffffffd555
const P_1_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0d0088f51cbff34du64,
        0x258dd3db21a5d66bu64,
        0xb23ba5c279c2895fu64,
        0xb39869507b587b12u64,
        0x0f55ffff58a9ffffu64,
        0xdcff7fffffffd555u64
    ]
));

//(p + 1) / 4 : 0680447a8e5ff9a6 92c6e9ed90d2eb35 d91dd2e13ce144af d9cc34a83dac3d89 07aaffffac54ffff ee7fbfffffffeaab
const P_1_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64,
        0x92c6e9ed90d2eb35u64,
        0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64,
        0x07aaffffac54ffffu64,
        0xee7fbfffffffeaabu64
    ]
));

//(p - 3) / 4 : 0680447a8e5ff9a6 92c6e9ed90d2eb35 d91dd2e13ce144af d9cc34a83dac3d89 07aaffffac54ffff ee7fbfffffffeaaa
const P_3_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64,
        0x92c6e9ed90d2eb35u64,
        0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64,
        0x07aaffffac54ffffu64,
        0xee7fbfffffffeaaau64
    ]
));

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.4.1
pub fn expand_message_xmd(msg: &ByteSeq, dst: &ByteSeq, len_in_bytes: usize) -> ByteSeq {
    let ell = (len_in_bytes + B_IN_BYTES - 1) / B_IN_BYTES; // ceil(len_in_bytes / b_in_bytes)
                                                            // must be that ell <= 255
    let dst_prime = dst.push(&U8_from_usize(dst.len())); // DST || I2OSP(len(DST), 1)
    let z_pad = ByteSeq::new(S_IN_BYTES); // I2OSP(0, s_in_bytes)
    let mut l_i_b_str = ByteSeq::new(2);
    l_i_b_str[0] = U8_from_usize(len_in_bytes / 256);
    l_i_b_str[1] = U8_from_usize(len_in_bytes); // I2OSP(len_in_bytes, 2)
    let msg_prime = z_pad
        .concat(msg)
        .concat(&l_i_b_str)
        .concat(&ByteSeq::new(1))
        .concat(&dst_prime); // Z_pad || msg || l_i_b_str || 0 || dst_prime
    let b_0 = ByteSeq::from_seq(&hash(&msg_prime)); // H(msg_prime)
    let mut b_i = ByteSeq::from_seq(&hash(&b_0.push(&U8(1u8)).concat(&dst_prime))); // H(b_0 || 1 || dst_prime)
    let mut uniform_bytes = ByteSeq::from_seq(&b_i);
    for i in 2..(ell + 1) {
        let t = ByteSeq::from_seq(&b_0);
        b_i = ByteSeq::from_seq(&hash(&(t ^ b_i).push(&U8_from_usize(i)).concat(&dst_prime))); //H((b_0 ^ b_(i-1)) || 1 || dst_prime)
        uniform_bytes = uniform_bytes.concat(&b_i);
    }
    uniform_bytes.truncate(len_in_bytes)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.3
pub fn fp_hash_to_field(msg: &ByteSeq, dst: &ByteSeq, count: usize) -> Seq<Fp> {
    let len_in_bytes = count * L; // count * m * L
    let uniform_bytes = expand_message_xmd(msg, dst, len_in_bytes);
    let mut output = Seq::<Fp>::new(count);
    for i in 0..count {
        // m = 1, so no loop
        let elm_offset = L * i; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let u_i =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output[i] = u_i;
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

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.1
fn g1_map_to_curve(u: Fp) -> G1 {
    let z = Fp::ZERO() - Fp::from_literal(3u128);
    let gz = g1_curve_func(z);
    let tv1 = u * u * gz;
    let tv2 = Fp::ONE() + tv1;
    let tv1 = Fp::ONE() - tv1;
    let tv3 = (tv1 * tv2).inv();
    let mut tv4 = fp_sqrt((Fp::ZERO() - gz) * (Fp::from_literal(3u128) * z * z)); // sqrt(-g(Z) * (3 * Z^2 + 4 * A)) #Could be pre-computed
    if fp_sgn0(tv4) {
        tv4 = Fp::ZERO() - tv4;
    }
    let tv5 = u * tv1 * tv3 * tv4;
    let tv6 = (Fp::ZERO() - Fp::from_literal(4u128)) * gz * (Fp::from_literal(3u128) * z * z).inv(); // -4 * g(Z) / (3 * Z^2 + 4 * A) #Could be pre-computed
    let x1 = (Fp::ZERO() - z) * Fp::TWO().inv() - tv5;
    let x2 = (Fp::ZERO() - z) * Fp::TWO().inv() + tv5;
    let x3 = z + tv6 * (tv2 * tv2 * tv3) * (tv2 * tv2 * tv3);
    let x = if fp_is_square(g1_curve_func(x1)) {
        x1
    } else {
        if fp_is_square(g1_curve_func(x2)) {
            x2
        } else {
            x3
        }
    };
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

//  https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g1_hash_to_curve(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 2);
    let q0 = g1_map_to_curve(u[0]);
    let q1 = g1_map_to_curve(u[1]);
    let r = g1add(q0, q1);
    let p = g1_clear_cofactor(r);
    p
}

pub fn g1_encode_to_curve(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 1);
    let q = g1_map_to_curve(u[0]);
    let p = g1_clear_cofactor(q);
    p
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.3
pub fn fp2_hash_to_field(msg: &ByteSeq, dst: &ByteSeq, count: usize) -> Seq<Fp2> {
    let len_in_bytes = count * 2 * L; // count * m * L
    let uniform_bytes = expand_message_xmd(msg, dst, len_in_bytes);
    let mut output = Seq::<Fp2>::new(count);
    for i in 0..count {
        // m = 2
        let elm_offset = L * i * 2; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_1 =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p

        let elm_offset = L * (1 + i * 2); // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_2 =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output[i] = (e_1, e_2);
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

// y^2 = g(x) = x^3 + 4(1 + I)
pub fn g2_curve_func(x: Fp2) -> Fp2 {
    fp2add(
        fp2mul(x, fp2mul(x, x)),
        (Fp::from_literal(4u128), Fp::from_literal(4u128)),
    )
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.1
fn g2_map_to_curve(u: Fp2) -> G2 {
    let z = fp2neg(fp2fromfp(Fp::ONE())); //-1
    let gz = g2_curve_func(z); //g(z)
    let tv1 = fp2mul(fp2mul(u, u), gz); // u^2 * g(z)
    let tv2 = fp2add(fp2fromfp(Fp::ONE()), tv1); // 1 + tv1
    let tv1 = fp2sub(fp2fromfp(Fp::ONE()), tv1); // 1 - tv1
    let tv3 = fp2inv(fp2mul(tv1, tv2)); // inv0(tv1 * tv2)
    let mut tv4 = fp2_sqrt(fp2mul(
        fp2neg(gz),
        fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(z, z)),
    )); // sqrt(-g(Z) * (3 * Z^2)) #Could be pre-computed
    if fp2_sgn0(tv4) {
        tv4 = fp2neg(tv4);
    }
    let tv5 = fp2mul(fp2mul(fp2mul(u, tv1), tv3), tv4); //u * tv1 * tv3 * tv4
    let tv6 = fp2mul(
        fp2mul(fp2neg(fp2fromfp(Fp::from_literal(4u128))), gz),
        fp2inv(fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(z, z))),
    ); // -4 * g(Z) / (3 * Z^2) #Could be pre-computed
    let x1 = fp2sub(fp2mul(fp2neg(z), fp2inv(fp2fromfp(Fp::TWO()))), tv5); // -Z / 2 - tv5
    let x2 = fp2add(fp2mul(fp2neg(z), fp2inv(fp2fromfp(Fp::TWO()))), tv5); // -Z / 2 - tv5
    let tv7 = fp2mul(fp2mul(tv2, tv2), tv3);
    let x3 = fp2add(z, fp2mul(tv6, fp2mul(tv7, tv7))); // z + tv6 * (tv2^2 * tv3)^2
    let x = if fp2_is_square(g2_curve_func(x1)) {
        x1
    } else {
        if fp2_is_square(g2_curve_func(x2)) {
            x2
        } else {
            x3
        }
    };
    let mut y = fp2_sqrt(g2_curve_func(x)); //sqrt(g(x))
    if fp2_sgn0(u) != fp2_sgn0(y) {
        y = fp2neg(y);
    }
    (x, y, false)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-G.3
fn psi(p: G2) -> G2 {
    let c1 = fp2inv(fp2exp(
        (Fp::ONE(), Fp::ONE()),
        (Fp::ZERO() - Fp::ONE()) * (Fp::from_literal(3u128)).inv(),
    )); // 1 / (1 + I)^((p - 1) / 3) #Could be pre-computed
    let c2 = fp2inv(fp2exp(
        (Fp::ONE(), Fp::ONE()),
        (Fp::ZERO() - Fp::ONE()) * (Fp::TWO()).inv(),
    )); // 1 / (1 + I)^((p - 1) / 2) #Could be pre-computed
    let (x, y, inf) = p;
    let qx = fp2mul(c1, fp2conjugate(x));
    let qy = fp2mul(c2, fp2conjugate(y));
    (qx, qy, inf)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-G.3
fn g2_clear_cofactor(p: G2) -> G2 {
    let c1 = Scalar::from_literal(0xd201000000010000u128);
    let t1 = g2mul(c1, p);
    let t1 = g2neg(t1); //neg since c1 is actually negative
    let t2 = psi(p);
    let t3 = g2double(p);
    let t3 = psi(psi(t3));
    let t3 = g2add(t3, g2neg(t2));
    let t2 = g2add(t1, t2);
    let t2 = g2mul(c1, t2);
    let t2 = g2neg(t2); //neg since c1 is actually negative
    let t3 = g2add(t3, t2);
    let t3 = g2add(t3, g2neg(t1));
    let q = g2add(t3, g2neg(p));
    q
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g2_hash_to_curve(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 2);
    let q0 = g2_map_to_curve(u[0]);
    let q1 = g2_map_to_curve(u[1]);
    let r = g2add(q0, q1);
    let p = g2_clear_cofactor(r);
    p
}

pub fn g2_encode_to_curve(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 1);
    let q = g2_map_to_curve(u[0]);
    let p = g2_clear_cofactor(q);
    p
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
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-K.1
    fn test_expand_message() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-expander-SHA256-128");
        let len_in_bytes = 0x20;
        let msg = ByteSeq::from_public_slice(b"");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "eff31487c770a893cfb36f912fbfcbff40d5661771ca4b2cb4eafe524333f5c1";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "b23a1d2b4d97b2ef7785562a7e8bac7eed54ed6e97e29aa51bfe3f12ddad1ff9";
        assert_eq!(expm.to_hex(), result);

        let len_in_bytes = 0x80;
        let msg = ByteSeq::from_public_slice(b"");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbee0d121587713a3e0dd4d5e69e93eb7cd4f5df4\
            cd103e188cf60cb02edc3edf18eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dcc541708d3491184472\
            c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "ef904a29bffc4cf9ee82832451c946ac3c8f8058ae97d8d629831a74c6572bd9ebd0df635cd1f208e2038e760c4994984ce73f\
            0d55ea9f22af83ba4734569d4bc95e18350f740c07eef653cbb9f87910d833751825f0ebefa1abe5420bb52be14cf489b37fe1a72f7d\
            e2d10be453b2c9d9eb20c7e3f6edc5a60629178d9478df";
        assert_eq!(expm.to_hex(), result);
    }

    #[test]
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.9.1
    fn test_fp_hash_to_field() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_");
        let msg = ByteSeq::from_public_slice(b"");
        let count = 2;
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "0ba14bd907ad64a016293ee7c2d276b8eae71f25a4b941eece7b0d89f17f75cb3ae5438a614fb61d6835ad59f29c564f");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "019b9bd7979f12657976de2884c7cce192b82c177c80e0ec604436a7f538d231552f0d96d9f7babe5fa3b19b3ff25ac9");

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "062d1865eb80ebfa73dcfc45db1ad4266b9f3a93219976a3790ab8d52d3e5f1e62f3b01795e36834b17b70e7b76246d4");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "0cdc3e2f271f29c4ff75020857ce6c5d36008c9b48385ea2f2bf6f96f428a3deb798aa033cd482d1cdc8b30178b08e3a");

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "010476f6a060453c0b1ad0b628f3e57c23039ee16eea5e71bb87c3b5419b1255dc0e5883322e563b84a29543823c0e86");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "0b1a912064fb0554b180e07af7e787f1f883a0470759c03c1b6509eb8ce980d1670305ae7b928226bb58fdc0a419f46e");
    }

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
        assert_eq!(k * k, x);
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
        assert_eq!(fp2mul(k, k), y);
    }

    #[test]
    fn test_g1_correct_z() {
        let z = Fp::ZERO() - Fp::from_literal(3);
        let gz = g1_curve_func(z);
        assert!(gz != Fp::ZERO());
        let t = (Fp::ZERO() - (Fp::from_literal(3) * z * z)) / (Fp::from_literal(4) * gz);
        assert!(t != Fp::ZERO());
        assert!(fp_is_square(t));
        assert!(fp_is_square(gz) || fp_is_square(g1_curve_func((Fp::ZERO() - z) / Fp::TWO())));
    }

    #[test]
    fn test_g1_map_to_curve() {
        let u = Fp::from_literal(3082);
        let (x, y, _) = g1_map_to_curve(u);
        assert_eq!(y * y, x * x * x + Fp::from_literal(4));
    }

    #[quickcheck]
    fn test_prop_g1_map_to_curve(a: u128) -> bool {
        let u = Fp::from_literal(a);
        let (x, y, _) = g1_map_to_curve(u);
        y * y == x * x * x + Fp::from_literal(4)
    }

    #[test]
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.9.2
    fn test_fp2_hash_to_field() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_");
        let msg = ByteSeq::from_public_slice(b"");
        let count = 2;
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "02f99798e8a5acdeed60d7e18e9120521ba1f47ec090984662846bc825de191b5b7641148c0dbc237726a334473eee94");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "145a81e418d4010cc027a68f14391b30074e89e60ee7a22f87217b2f6eb0c4b94c9115b436e6fa4607e95a98de30a435");

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "0313d9325081b415bfd4e5364efaef392ecf69b087496973b229303e1816d2080971470f7da112c4eb43053130b785e1");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "062f84cb21ed89406890c051a0e8b9cf6c575cf6e8e18ecf63ba86826b0ae02548d83b483b79e48512b82a6c0686df8f");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "1739123845406baa7be5c5dc74492051b6d42504de008c635f3535bb831d478a341420e67dcc7b46b2e8cba5379cca97");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "01897665d9cb5db16a27657760bbea7951f67ad68f8d55f7113f24ba6ddd82caef240a9bfa627972279974894701d975");

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "025820cefc7d06fd38de7d8e370e0da8a52498be9b53cba9927b2ef5c6de1e12e12f188bbc7bc923864883c57e49e253");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "034147b77ce337a52e5948f66db0bab47a8d038e712123bb381899b6ab5ad20f02805601e6104c29df18c254b8618c7b");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "0930315cae1f9a6017c3f0c8f2314baa130e1cf13f6532bff0a8a1790cd70af918088c3db94bda214e896e1543629795");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "10c4df2cacf67ea3cb3108b00d4cbd0b3968031ebc8eac4b1ebcefe84d6b715fde66bef0219951ece29d1facc8a520ef");
    }

    #[test]
    fn test_g2_correct_z() {
        let z = fp2neg(fp2fromfp(Fp::ONE()));
        let gz = g2_curve_func(z);
        assert!(gz != fp2zero());
        let t = fp2mul(
            fp2neg(fp2mul(fp2fromfp(Fp::from_literal(3)), fp2mul(z, z))),
            fp2inv(fp2mul(fp2fromfp(Fp::from_literal(4)), gz)),
        );
        assert!(t != fp2zero());
        assert!(fp2_is_square(t));
        assert!(fp2_is_square(gz));
    }

    #[test]
    fn test_g2_map_to_curve() {
        let u1 = Fp::from_literal(3082);
        let u2 = Fp::from_literal(4021);
        let (x, y, _) = g2_map_to_curve((u1, u2));
        assert_eq!(
            fp2mul(y, y),
            fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4))
            )
        );
    }

    #[quickcheck]
    fn test_prop_g2_map_to_curve(a: u128, b: u128) -> bool {
        let u1 = Fp::from_literal(a);
        let u2 = Fp::from_literal(b);
        let (x, y, _) = g2_map_to_curve((u1, u2));
        fp2mul(y, y)
            == fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4)),
            )
    }
}
