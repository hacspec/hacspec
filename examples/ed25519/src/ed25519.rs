//! This crate gives a specification for the EdDSA signature scheme ed25519.
//! As there is no proper consensus for the verification algorithm, it has been implemented
//! in multiple ways.
//! - zcash_verify implements the ZIP-0215 standard (<https://zips.z.cash/zip-0215>)
//! - ietf_cofactored_verify and ietf_cofactorless_verify both implement the ietf standard.
//! (<https://datatracker.ietf.org/doc/rfc8032>). However as the standard writes:
//!
//!     > Check the group equation \[8\]\[S\]B = \[8\]R + \[8\]\[k\]A'.  It's sufficient, but not,
//!     > required to instead check \[S\]B = R + \[k\]A'.
//!
//!     they differ in which of the verification equations they use.
//! - alg2_verify implements algorithm 2 from the paper <https://eprint.iacr.org/2020/1244.pdf>.
//!
//! The different implementations and specifications differ in three ways:
//! - Cofactored/cofactorless verification -- (Using \[8\]\[S\]B = \[8\]R + \[8\]\[H(R, A, msg)\]A
//! or \[S\]B = R + \[H(R, A, msg)\]A as the verification check).
//! - Accepting/rejecting non-canonical encodings of points.
//! - Accepting/rejecting small-order points.
//!
//! For each of the single signature verification algorithms, their corresponding batch
//! verification algorithm has also been implemented. However one should not use cofactorless
//! batch verification as on some inputs it is flaky (ie. it can both accept and reject the signature
//! non-deterministically). The reason this is included is for completeness sake, to show that it
//! is indeed flaky, and because multiple libraries implement this batch verification (eg. the dalek
//! library). Cofactored batch verification does not have this problem.
//!
//! The paper <https://eprint.iacr.org/2020/1244.pdf> shows why cofactorless batch verification
//! does not work. It also provides test vectors for edge cases and compares various implementations
//! on these.
//!
//! # Examples
//! ```
//! use hacspec_lib::*;
//! use hacspec_ed25519::*;
//!
//! let sk = SecretKey::from_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
//! // or alternatively SecretKey::from_public_slice(...);
//! let msg = ByteSeq::from_public_slice(b"hello world");
//! let sig = sign(sk, &msg);
//! let pk = secret_to_public(sk);
//! assert!(zcash_verify(pk, sig, &msg).is_ok());
//! ```
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
    s[31] = s[31] ^ (is_negative(x) << 7); // setting top bit
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

fn check_canonical_point(mut x: CompressedEdPoint) -> bool {
    x[31] = x[31] & U8(127u8);
    let x = BigInteger::from_byte_seq_le(x);
    x < BigInteger::from_byte_seq_le(CONSTANT_P)
}

fn decompress(q: CompressedEdPoint) -> Option<EdPoint> {
    let d = Ed25519FieldElement::from_byte_seq_le(CONSTANT_D);

    let x_s = (q[31usize] & U8(128u8)) >> 7;
    let mut y_s = q;
    y_s[31] = y_s[31] & U8(127u8);
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
    y_s[31] = y_s[31] & U8(127u8);
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
    s[0] = s[0] & U8(248u8);
    s[31] = s[31] & U8(127u8);
    s[31] = s[31] | U8(64u8);
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

/// Sign a message under a secret key.
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

/// Cofactored verification.
/// Allows non-canonical encoding of points.
/// Allows small-order points.
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

/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
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

/// Cofactorless verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
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

/// Algorithm 2 from <https://eprint.iacr.org/2020/1244.pdf>.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Rejects small-order points for the public key.
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
pub struct BatchEntry(pub PublicKey, pub ByteSeq, pub Signature);

/// Batch verification.
/// Cofactored verification.
/// Allows non-canonical encoding of points.
/// Allows small-order points.
pub fn zcash_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
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

/// Batch verification.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
pub fn ietf_cofactored_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
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
    let check = point_mul_by_cofactor(point_add(point_neg(sb), point_add(r_sum, a_sum)));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Batch verification.
/// Cofactorless verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
/// One should not use this as it can be flaky.
pub fn ietf_cofactorless_batch_verify(
    entries: &Seq<BatchEntry>,
    entropy: &ByteSeq,
) -> VerifyResult {
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

/// Batch verification.
/// Algorithm 3 from <https://eprint.iacr.org/2020/1244.pdf>.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Rejects small-order points for the public key.
pub fn alg3_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
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

#[cfg(test)]
mod test {
    use super::*;
    use hacspec_dev::prelude::*;

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

    // Test that shows that cofactorless batch verification can be flaky.
    // ie. on the same input it can both accept and reject.
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
            let entropy = rand::random_byte_vec(16);
            let entropy = ByteSeq::from_public_slice(&entropy);
            if ietf_cofactorless_batch_verify(&entry, &entropy).is_ok() {
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
            let entropy = rand::random_byte_vec(16);
            let entropy = ByteSeq::from_public_slice(&entropy);
            if ietf_cofactored_batch_verify(&entry, &entropy).is_ok() {
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
