use hacspec_lib::*;
use hacspec_sha512::*;

public_nat_mod!(
    type_name: Ed25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);
public_nat_mod!(
    type_name: BigScalar,
    type_of_canvas: BigScalarCanvas,
    bit_size_of_field: 512,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);
public_nat_mod!(
    type_name: BigInteger,
    type_of_canvas: BigIntegerCanvas,
    bit_size_of_field: 256,
    modulo_value: "8000000000000000000000000000000080000000000000000000000000000000"
);

type EdPoint = (
    Ed25519FieldElement,
    Ed25519FieldElement,
    Ed25519FieldElement,
    Ed25519FieldElement,
);

bytes!(CompressedEdPoint, 32);
bytes!(SerializedScalar, 32);
bytes!(Signature, 64);

pub type PublicKey = CompressedEdPoint;
pub type SecretKey = SerializedScalar;

#[derive(Debug)]
pub enum Error {
    InvalidPublickey,
    InvalidSignature,
    InvalidS,
    InvalidR,
    SmallOrderPoint,
    NotEnoughRandomness,
}

pub type VerifyResult = Result<(), Error>;

#[rustfmt::skip]
const BASE: CompressedEdPoint = CompressedEdPoint(secret_array!(
    U8, 
    [
        0x58u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8,
        0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8, 0x66u8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xedu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_L: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xedu8, 0xd3u8, 0xf5u8, 0x5cu8, 0x1au8, 0x63u8, 0x12u8, 0x58u8,
        0xd6u8, 0x9cu8, 0xf7u8, 0xa2u8, 0xdeu8, 0xf9u8, 0xdeu8, 0x14u8,
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 
        0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x10u8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P3_8: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xfeu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x0fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_P1_4: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xfbu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x1fu8 
    ]
));

#[rustfmt::skip]
const CONSTANT_D: SerializedScalar = SerializedScalar(secret_array!(
    U8, 
    [
        0xa3u8, 0x78u8, 0x59u8, 0x13u8, 0xcau8, 0x4du8, 0xebu8, 0x75u8, 
        0xabu8, 0xd8u8, 0x41u8, 0x41u8, 0x4du8, 0x0au8, 0x70u8, 0x00u8, 
        0x98u8, 0xe8u8, 0x79u8, 0x77u8, 0x79u8, 0x40u8, 0xc7u8, 0x8cu8, 
        0x73u8, 0xfeu8, 0x6fu8, 0x2bu8, 0xeeu8, 0x6cu8, 0x03u8, 0x52u8 
    ]
));

fn is_negative(x: Ed25519FieldElement) -> U8 {
    if x.bit(0) {
        U8(1u8)
    } else {
        U8(0u8)
    }
}

fn compress(p: EdPoint) -> CompressedEdPoint {
    let (x, y, z, _) = p;
    let z_inv = z.inv();
    let x = x * z_inv;
    let y = y * z_inv;
    let mut s: ByteSeq = y.to_byte_seq_le();
    s[31usize] = s[31usize] ^ (is_negative(x) << 7); // setting top bit
    CompressedEdPoint::from_slice(&s, 0, 32)
}

fn sqrt(a: Ed25519FieldElement) -> Option<Ed25519FieldElement> {
    let p3_8 = Ed25519FieldElement::from_byte_seq_le(CONSTANT_P3_8);
    let p1_4 = Ed25519FieldElement::from_byte_seq_le(CONSTANT_P1_4);

    let x_c = a.pow_self(p3_8);
    let mut result: Option<Ed25519FieldElement> = Option::<Ed25519FieldElement>::None;
    if x_c * x_c == a {
        result = Some(x_c);
    };
    if x_c * x_c == Ed25519FieldElement::ZERO() - a {
        let x = Ed25519FieldElement::TWO().pow_self(p1_4) * x_c;
        result = Some(x);
    }
    result
}

fn check_canonical_point(x: CompressedEdPoint) -> bool {
    let mut x = x;
    x[31usize] = x[31usize] & U8(127u8);
    let x = BigInteger::from_byte_seq_le(x);
    x < BigInteger::from_byte_seq_le(CONSTANT_P)
}

fn decompress(q: CompressedEdPoint) -> Option<EdPoint> {
    let d = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);

    let x_s = (q[31usize] & U8(128u8)) >> 7;
    let mut y_s = q;
    y_s[31usize] = y_s[31usize] & U8(127u8);
    if !check_canonical_point(y_s) {
        Option::<EdPoint>::None?;
    }
    let y = Ed25519FieldElement::from_byte_seq_le(y_s);
    let z = Ed25519FieldElement::ONE();
    let yy = y * y;
    let u = yy - z;
    let v = d * yy + z;
    let xx = u * v.inv();
    let mut x = sqrt(xx)?;
    let x_r = is_negative(x);
    if x == Ed25519FieldElement::ZERO() && x_s.declassify() == 1u8 {
        Option::<EdPoint>::None?;
    }
    if x_r.declassify() != x_s.declassify() {
        x = Ed25519FieldElement::ZERO() - x;
    }
    Some((x, y, z, x * y))
}

// Allows decompression of non-canonical points
fn decompress_non_canonical(p: CompressedEdPoint) -> Option<EdPoint> {
    let d = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);

    let x_s = (p[31usize] & U8(128u8)) >> 7;
    let mut y_s = p;
    y_s[31usize] = y_s[31usize] & U8(127u8);
    let y = Ed25519FieldElement::from_byte_seq_le(y_s);
    let z = Ed25519FieldElement::ONE();
    let yy = y * y;
    let u = yy - z;
    let v = d * yy + z;
    let xx = u * v.inv();
    let mut x = sqrt(xx)?;
    let x_r = is_negative(x);
    if x_r.declassify() != x_s.declassify() {
        x = Ed25519FieldElement::ZERO() - x;
    }
    Some((x, y, z, x * y))
}

fn point_add(p: EdPoint, q: EdPoint) -> EdPoint {
    let d_c = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);
    let two = Ed25519FieldElement::TWO();

    let (x1, y1, z1, t1) = p;
    let (x2, y2, z2, t2) = q;
    let a = (y1 - x1) * (y2 - x2);
    let b = (y1 + x1) * (y2 + x2);
    let c = t1 * two * d_c * t2;
    let d = z1 * two * z2;
    let e = b - a;
    let f = d - c;
    let g = d + c;
    let h = b + a;
    let x3 = e * f;
    let y3 = g * h;
    let t3 = e * h;
    let z3 = f * g;
    (x3, y3, z3, t3)
}

fn point_identity() -> EdPoint {
    (
        Ed25519FieldElement::ZERO(),
        Ed25519FieldElement::ONE(),
        Ed25519FieldElement::ONE(),
        Ed25519FieldElement::ZERO(),
    )
}

fn point_mul(s: Scalar, p: EdPoint) -> EdPoint {
    let mut p = p;
    let mut q = point_identity();
    for i in 0..256 {
        if s.bit(i) {
            q = point_add(q, p);
        }
        p = point_add(p, p);
    }
    q
}

fn point_mul_by_cofactor(p: EdPoint) -> EdPoint {
    let p2 = point_add(p, p);
    let p4 = point_add(p2, p2);
    let p8 = point_add(p4, p4);
    p8
}

fn point_neg(p: EdPoint) -> EdPoint {
    let (x, y, z, t) = p;
    (
        Ed25519FieldElement::ZERO() - x,
        y,
        z,
        Ed25519FieldElement::ZERO() - t,
    )
}

fn point_eq(p: EdPoint, q: EdPoint) -> bool {
    let (x1, y1, z1, _) = p;
    let (x2, y2, z2, _) = q;
    x1 * z2 == x2 * z1 && y1 * z2 == y2 * z1
}

fn secret_expand(sk: SecretKey) -> (SerializedScalar, SerializedScalar) {
    let h = sha512(&ByteSeq::from_slice(&sk, 0, 32));
    let h_d = SerializedScalar::from_slice(&h, 32, 32);
    let mut s = SerializedScalar::from_slice(&h, 0, 32);
    s[0usize] = s[0usize] & U8(248u8);
    s[31usize] = s[31usize] & U8(127u8);
    s[31usize] = s[31usize] | U8(64u8);
    (s, h_d)
}

pub fn secret_to_public(sk: SecretKey) -> PublicKey {
    let (s, _) = secret_expand(sk);
    let base = decompress(BASE).unwrap();
    let ss = Scalar::from_byte_seq_le(s);
    let a = point_mul(ss, base);
    compress(a)
}

fn check_canonical_scalar(s: SerializedScalar) -> bool {
    if (s[31usize] & U8(224u8)).declassify() != 0u8 {
        false
    } else {
        BigInteger::from_byte_seq_le(s) < BigInteger::from_byte_seq_le(CONSTANT_L)
    }
}

fn scalar_from_hash(h: Sha512Digest) -> Scalar {
    let s = BigScalar::from_byte_seq_le(h);
    Scalar::from_byte_seq_le(s.to_byte_seq_le().slice(0, 32))
}

pub fn sign(sk: SecretKey, msg: &ByteSeq) -> Signature {
    let (a, prefix) = secret_expand(sk);
    let a = Scalar::from_byte_seq_le(a);
    let b = decompress(BASE).unwrap();
    let a_p = compress(point_mul(a, b));
    let r = scalar_from_hash(sha512(&prefix.concat(msg)));
    let r_p = point_mul(r, b);
    let r_s = compress(r_p);
    let h = scalar_from_hash(sha512(&r_s.concat(&a_p).concat(msg)));
    let s = r + h * a;
    let s_bytes = s.to_byte_seq_le().slice(0, 32);
    Signature::new().update(0, &r_s).update(32, &s_bytes)
}

// Allows non-canonical encoding of points
// Uses verification equation: [8][S]B = [8]R + [8][H(R, A, msg)]A
pub fn zcash_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress_non_canonical(BASE).unwrap();
    let a = decompress_non_canonical(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress_non_canonical(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

// Uses verification equation: [8][S]B = [8]R + [8][H(R, A, msg)]A
pub fn ietf_cofactored_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

// Uses verification equation: [S]B = R + [H(R, A, msg)]A
pub fn ietf_cofactorless_verify(
    pk: PublicKey,
    signature: Signature,
    msg: &ByteSeq,
) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul(s, b);
    let ka = point_mul(k, a);

    if point_eq(sb, point_add(r, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

fn is_identity(p: EdPoint) -> bool {
    point_eq(p, point_identity())
}

// Algorithm 2 from https://eprint.iacr.org/2020/1244.pdf
// Disallows the public key to a point with small-order (<= 8)
// Uses verification equation: [8][S]B = [8]R + [8][H(R, A, msg)]A
pub fn alg2_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    if is_identity(point_mul_by_cofactor(a)) {
        VerifyResult::Err(Error::SmallOrderPoint)?;
    }
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

#[derive(Default, Clone)]
pub struct BatchEntry(PublicKey, ByteSeq, Signature);

// Batch verification
// Uses verification equation: [8](- [sum z_j*S_j mod l]B + sum [z_j]R_j + sum [z_j*c_j mod l]A_j) = 0
pub fn batch_verify_zcash(entries: Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress_non_canonical(pk).ok_or(Error::InvalidPublickey)?;
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress_non_canonical(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;

        r_sum = point_add(r_sum, point_mul(z, r));

        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_mul_by_cofactor(point_add(point_neg(sb), point_add(r_sum, a_sum)));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

// Uses verification equation: (- [sum z_j*S_j mod l]B + sum [z_j]R_j + sum [z_j*c_j mod l]A_j) = 0
pub fn batch_verify_cofactorless(entries: Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;

        r_sum = point_add(r_sum, point_mul(z, r));

        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_add(point_neg(sb), point_add(r_sum, a_sum));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
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
    fn test_compress_decompress() {
        let sk = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));
        let b = decompress(BASE).unwrap();
        let a = point_mul(sk, b);
        let r = compress(a);
        assert!(point_eq(a, decompress(r).unwrap()));
    }

    #[test]
    fn test_secret_to_public() {
        let s = SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        );
        let result = CompressedEdPoint::from_hex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let a = secret_to_public(s);
        assert_bytes_eq!(a, result);

        let s = SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        );
        let result = CompressedEdPoint::from_hex(
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
        );
        let a = secret_to_public(s);
        assert_bytes_eq!(a, result);
    }

    #[test]
    fn test_sign() {
        let s = SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        );
        let msg = ByteSeq::from_public_slice(b"");
        let sig = sign(s, &msg);
        let result = Signature::from_hex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
            5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        assert_bytes_eq!(sig, result);

        let s = SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        );
        let msg = ByteSeq::from_hex("72");
        let sig = sign(s, &msg);
        let result = Signature::from_hex(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
            085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        assert_bytes_eq!(sig, result);

        let s = SerializedScalar::from_hex(
            "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
        );
        let msg = ByteSeq::from_hex("af82");
        let sig = sign(s, &msg);
        let result = Signature::from_hex(
            "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac\
            18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a",
        );
        assert_bytes_eq!(sig, result);
    }

    #[test]
    fn test_verify() {
        let a = CompressedEdPoint::from_hex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let msg = ByteSeq::from_hex("");
        let sig = Signature::from_hex(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
            5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let result = zcash_verify(a, sig, &msg);
        assert!(result.is_ok());

        let s = SerializedScalar::from_hex(
            "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
        );
        let a = secret_to_public(s);
        let msg = ByteSeq::from_hex("af82");
        let sig = sign(s, &msg);
        let sig_result = Signature::from_hex(
            "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac\
            18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a",
        );
        assert_bytes_eq!(sig, sig_result);
        assert!(zcash_verify(a, sig, &msg).is_ok());
    }

    #[quickcheck]
    fn test_sign_verify(sk: (u128, u128), msg: String) -> bool {
        let (sk1, sk2) = sk;
        let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
        let sk = SerializedScalar::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = &ByteSeq::from_public_slice(msg.as_bytes());
        let signature = sign(sk, &msg);
        zcash_verify(pk, signature, msg).is_ok()
    }

    #[quickcheck]
    fn test_sign_verify_cofactorless(sk: (u128, u128), msg: String) -> bool {
        let (sk1, sk2) = sk;
        let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
        let sk = SerializedScalar::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = &ByteSeq::from_public_slice(msg.as_bytes());
        let signature = sign(sk, &msg);
        ietf_cofactorless_verify(pk, signature, msg).is_ok()
    }

    //use rand::prelude::*;
    #[test]
    fn test_batch_zcash() {
        let entropy: [[u8; 16]; 32] = rand::random();
        let entropy = ByteSeq::from_public_slice(&entropy.concat());
        let mut entries = Seq::<BatchEntry>::new(32);
        for i in 0usize..32 {
            let sk: [u8; 32] = rand::random();
            let sk = SecretKey::from_public_slice(&sk);
            let pk = secret_to_public(sk);
            let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
            let sig = sign(sk, &msg);
            entries[i] = BatchEntry(pk, msg, sig);
        }
        assert!(batch_verify_zcash(entries, &entropy).is_ok());
    }

    #[test]
    fn test_batch_bad_zcash() {
        let entropy: [[u8; 16]; 32] = rand::random();
        let entropy = ByteSeq::from_public_slice(&entropy.concat());
        let mut entries = Seq::<BatchEntry>::new(32);
        let bad_index = 10;
        for i in 0usize..32 {
            let sk: [u8; 32] = rand::random();
            let sk = SecretKey::from_public_slice(&sk);
            let pk = secret_to_public(sk);
            let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
            let sig = if i != bad_index {
                sign(sk, &msg)
            } else {
                sign(sk, &ByteSeq::from_public_slice(b"badmsg"))
            };
            entries[i] = BatchEntry(pk, msg, sig);
        }
        assert!(batch_verify_zcash(entries.clone(), &entropy).is_err());
        for i in 0usize..32 {
            let BatchEntry(pk, msg, signature) = entries[i].clone();
            if i != bad_index {
                assert!(zcash_verify(pk, signature, &msg).is_ok())
            } else {
                assert!(zcash_verify(pk, signature, &msg).is_err())
            }
        }
    }

    #[test]
    fn test_batch_cofactorless() {
        let entropy: [[u8; 16]; 32] = rand::random();
        let entropy = ByteSeq::from_public_slice(&entropy.concat());
        let mut entries = Seq::<BatchEntry>::new(32);
        for i in 0usize..32 {
            let sk: [u8; 32] = rand::random();
            let sk = SecretKey::from_public_slice(&sk);
            let pk = secret_to_public(sk);
            let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
            let sig = sign(sk, &msg);
            entries[i] = BatchEntry(pk, msg, sig);
        }
        let result = batch_verify_cofactorless(entries, &entropy);
        println!("{:?}", result);
        assert!(result.is_ok());
    }

    #[test]
    fn test_batch_single_cofactorless() {
        let entropy: [u8; 16] = rand::random();
        let entropy = ByteSeq::from_public_slice(&entropy);
        let sk: [u8; 32] = rand::random();
        let sk = SecretKey::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
        let sig = sign(sk, &msg);

        let mut entries = Seq::<BatchEntry>::new(1);
        entries[0] = BatchEntry(pk, msg.clone(), sig);
        let result = batch_verify_cofactorless(entries, &entropy);

        assert!(ietf_cofactorless_verify(pk, sig, &msg).is_ok());

        println!("{:?}", result);
        assert!(result.is_ok());
    }

    #[test]
    fn test_cofactorless_flaky() {
        let b = decompress(BASE).unwrap();
        let small_order_point = decompress(CompressedEdPoint::from_hex(
            "C7176A703D4DD84FBA3C0B760D10670F2A2053FA2C39CCC64EC7FD7792AC037A",
        ))
        .unwrap();
        let msg = ByteSeq::from_public_slice(b"hello test");

        let s = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));

        let r = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        ));

        let ap = point_add(point_mul(s, b), small_order_point);
        let rp = point_mul(r, b);
        let ap_bytes = compress(ap);
        let rp_bytes = compress(rp);
        let c = scalar_from_hash(sha512(&rp_bytes.concat(&ap_bytes).concat(&msg)));

        let sp = r + c * s;
        let sig = Signature::new()
            .update(0, &rp_bytes)
            .update(32, &sp.to_byte_seq_le());
        assert!(ietf_cofactorless_verify(ap_bytes, sig, &msg).is_err());

        let mut entry = Seq::<BatchEntry>::new(1);
        entry[0] = BatchEntry(ap_bytes, msg, sig);
        let mut no_f = 0;
        let mut no_t = 0;
        for _ in 0..64 {
            let entropy: [u8; 16] = rand::random();
            let entropy = ByteSeq::from_public_slice(&entropy);
            if batch_verify_cofactorless(entry.clone(), &entropy).is_ok() {
                no_t += 1;
            } else {
                no_f += 1;
            }
        }
        println!("no_t: {}\nno_f: {}", no_t, no_f);
        assert!(0 < no_t);
        assert!(0 < no_f);
    }

    #[test]
    fn test_cofactored_not_flaky() {
        let b = decompress(BASE).unwrap();
        let small_order_point = decompress(CompressedEdPoint::from_hex(
            "C7176A703D4DD84FBA3C0B760D10670F2A2053FA2C39CCC64EC7FD7792AC037A",
        ))
        .unwrap();
        let msg = ByteSeq::from_public_slice(b"hello test");

        let s = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));

        let r = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        ));

        let ap = point_add(point_mul(s, b), small_order_point);
        let rp = point_mul(r, b);
        let ap_bytes = compress(ap);
        let rp_bytes = compress(rp);
        let c = scalar_from_hash(sha512(&rp_bytes.concat(&ap_bytes).concat(&msg)));

        let sp = r + c * s;
        let sig = Signature::new()
            .update(0, &rp_bytes)
            .update(32, &sp.to_byte_seq_le());
        assert!(zcash_verify(ap_bytes, sig, &msg).is_ok());

        let mut entry = Seq::<BatchEntry>::new(1);
        entry[0] = BatchEntry(ap_bytes, msg, sig);
        let mut no_f = 0;
        let mut no_t = 0;
        for _ in 0..32 {
            let entropy: [u8; 16] = rand::random();
            let entropy = ByteSeq::from_public_slice(&entropy);
            if batch_verify_zcash(entry.clone(), &entropy).is_ok() {
                no_t += 1;
            } else {
                no_f += 1;
            }
        }
        println!("no_t: {}\nno_f: {}", no_t, no_f);
        assert!(0 < no_t);
        assert!(0 == no_f);
    }
}
