use hacspec_lib::*;
use hacspec_bls12_381_hash::*;
use h2c_rust_ref::*;
use redox_ecc::ellipticcurve::EllipticCurve;
use redox_ecc::ops::FromFactory;

use pairing_plus::hash_to_curve::HashToCurve;
use pairing_plus::bls12_381::{G1, FqRepr, G2};
use pairing_plus::hash_to_field::{ExpandMsgXmd};
use sha2_8::Sha256;
use pairing_plus::{CurveProjective, CurveAffine};

use amcl::bls381::bls381::utils::{hash_to_curve_g1, deserialize_g1, hash_to_curve_g2, deserialize_g2};

use bls12_381::hash_to_curve::{HashToCurve as ZKHashToCurve, ExpandMsgXmd as ZKExpandMsgXmd};
use bls12_381::{G1Affine as ZKG1Affine, G1Projective as ZKG1Projective, G2Affine as ZKG2Affine, G2Projective as ZKG2Projective};
use sha2_9::Sha256 as ZKSha256;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;


#[test]
fn it_works() {
    let dst = b"zkcrypto-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg = b"hello world";
    let p = g2_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let t = [p.0.1.to_byte_seq_be().to_native(), p.0.0.to_byte_seq_be().to_native(), p.1.1.to_byte_seq_be().to_native(), p.1.0.to_byte_seq_be().to_native()].concat();
    let mut tv = [0; 192];
    tv.copy_from_slice(&t[0..192]);
    let ph = ZKG2Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG2Affine::from(<ZKG2Projective as ZKHashToCurve<ZKExpandMsgXmd<ZKSha256>>>::hash_to_curve(msg, dst));
    assert!(ph == q);
}

#[quickcheck]
fn test_equiv_armfazh_g1_sswu_ro(msg : String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SSWU_RO_"].get(dst);
    let curve = suite.get_curve();
    let f = curve.get_field();
    let msg: &[u8] = msg.as_bytes();

    let p = g1_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x: &str = &format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let y: &str = &format!("0x{}", p.1.to_byte_seq_be().to_hex());
    let hc = curve.new_point(f.from(x), f.from(y));
    let mut rustref = suite.hash(msg);
    rustref.normalize();
    rustref == hc
}

#[quickcheck]
fn test_equiv_armfazh_g1_sswu_nu(msg : String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SSWU_NU_"].get(dst);
    let curve = suite.get_curve();
    let f = curve.get_field();
    let msg: &[u8] = msg.as_bytes();

    let p = g1_encode_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x: &str = &format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let y: &str = &format!("0x{}", p.1.to_byte_seq_be().to_hex());
    let hc = curve.new_point(f.from(x), f.from(y));
    let mut rustref = suite.hash(msg);
    rustref.normalize();
    rustref == hc
}

#[quickcheck]
fn test_equiv_armfazh_g1_svdw_ro(msg : String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SVDW_RO_";
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SVDW_RO_"].get(dst);
    let curve = suite.get_curve();
    let f = curve.get_field();
    let msg: &[u8] = msg.as_bytes();

    let p = g1_hash_to_curve_svdw(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x: &str = &format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let y: &str = &format!("0x{}", p.1.to_byte_seq_be().to_hex());
    let hc = curve.new_point(f.from(x), f.from(y));
    let mut rustref = suite.hash(msg);
    rustref.normalize();
    rustref == hc
}

#[quickcheck]
fn test_equiv_armfazh_g1_svdw_nu(msg : String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SVDW_NU_";
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SVDW_NU_"].get(dst);
    let curve = suite.get_curve();
    let f = curve.get_field();
    let msg: &[u8] = msg.as_bytes();

    let p = g1_encode_to_curve_svdw(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x: &str = &format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let y: &str = &format!("0x{}", p.1.to_byte_seq_be().to_hex());
    let hc = curve.new_point(f.from(x), f.from(y));
    let mut rustref = suite.hash(msg);
    rustref.normalize();
    rustref == hc
}

#[quickcheck]
fn test_equiv_pairing_plus_g1_sswu_ro(msg : String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G1 as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve::<&[u8], &[u8]>(msg, dst).into_affine();
    let p = g1_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x = FqRepr::from(*q.as_tuple().0).to_string();
    let y = FqRepr::from(*q.as_tuple().1).to_string();
    let xh = format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let yh = format!("0x{}", p.1.to_byte_seq_be().to_hex());
    x == xh && y == yh
}

#[quickcheck]
fn test_equiv_pairing_plus_g1_sswu_nu(msg : String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G1 as HashToCurve<ExpandMsgXmd<Sha256>>>::encode_to_curve::<&[u8], &[u8]>(msg, dst).into_affine();
    let p = g1_encode_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x = FqRepr::from(*q.as_tuple().0).to_string();
    let y = FqRepr::from(*q.as_tuple().1).to_string();
    let xh = format!("0x{}", p.0.to_byte_seq_be().to_hex());
    let yh = format!("0x{}", p.1.to_byte_seq_be().to_hex());
    x == xh && y == yh
}

#[quickcheck]
fn test_equiv_pairing_plus_g2_sswu_ro(msg : String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G2 as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve::<&[u8], &[u8]>(msg, dst).into_affine();
    let p = g2_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x_r = FqRepr::from(q.as_tuple().0.c0).to_string();
    let x_i = FqRepr::from(q.as_tuple().0.c1).to_string();
    let y_r = FqRepr::from(q.as_tuple().1.c0).to_string();
    let y_i = FqRepr::from(q.as_tuple().1.c1).to_string();
    let xh_r = format!("0x{}", p.0.0.to_byte_seq_be().to_hex());
    let xh_i = format!("0x{}", p.0.1.to_byte_seq_be().to_hex());
    let yh_r = format!("0x{}", p.1.0.to_byte_seq_be().to_hex());
    let yh_i = format!("0x{}", p.1.1.to_byte_seq_be().to_hex());
    x_r == xh_r && x_i == xh_i && y_r == yh_r && y_i == yh_i
}

#[quickcheck]
fn test_equiv_pairing_plus_g2_sswu_nu(msg : String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G2_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G2 as HashToCurve<ExpandMsgXmd<Sha256>>>::encode_to_curve::<&[u8], &[u8]>(msg, dst).into_affine();
    let p = g2_encode_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x_r = FqRepr::from(q.as_tuple().0.c0).to_string();
    let x_i = FqRepr::from(q.as_tuple().0.c1).to_string();
    let y_r = FqRepr::from(q.as_tuple().1.c0).to_string();
    let y_i = FqRepr::from(q.as_tuple().1.c1).to_string();
    let xh_r = format!("0x{}", p.0.0.to_byte_seq_be().to_hex());
    let xh_i = format!("0x{}", p.0.1.to_byte_seq_be().to_hex());
    let yh_r = format!("0x{}", p.1.0.to_byte_seq_be().to_hex());
    let yh_i = format!("0x{}", p.1.1.to_byte_seq_be().to_hex());
    x_r == xh_r && x_i == xh_i && y_r == yh_r && y_i == yh_i
}

#[quickcheck]
fn test_equiv_apache_g1_sswu_ro(msg : String) -> bool {
    let dst = b"apache-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let tv =[p.0.to_byte_seq_be().to_native(), p.1.to_byte_seq_be().to_native()].concat();
    let ph = deserialize_g1(&tv).unwrap();
    let q = hash_to_curve_g1(msg, dst);
    ph == q
}

#[quickcheck]
fn test_equiv_apache_g2_sswu_ro(msg : String) -> bool {
    let dst = b"apache-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let tv =[p.0.1.to_byte_seq_be().to_native(), p.0.0.to_byte_seq_be().to_native(), p.1.1.to_byte_seq_be().to_native(), p.1.0.to_byte_seq_be().to_native()].concat();
    let ph = deserialize_g2(&tv).unwrap();
    let q = hash_to_curve_g2(msg, dst);
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g1_sswu_ro(msg : String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let t = [p.0.to_byte_seq_be().to_native(), p.1.to_byte_seq_be().to_native()].concat();
    let mut tv = [0; 96];
    tv.copy_from_slice(&t[0..96]);
    let ph = ZKG1Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG1Affine::from(<ZKG1Projective as ZKHashToCurve<ZKExpandMsgXmd<ZKSha256>>>::hash_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g1_sswu_nu(msg : String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_encode_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let t = [p.0.to_byte_seq_be().to_native(), p.1.to_byte_seq_be().to_native()].concat();
    let mut tv = [0; 96];
    tv.copy_from_slice(&t[0..96]);
    let ph = ZKG1Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG1Affine::from(<ZKG1Projective as ZKHashToCurve<ZKExpandMsgXmd<ZKSha256>>>::encode_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g2_sswu_ro(msg : String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let t = [p.0.1.to_byte_seq_be().to_native(), p.0.0.to_byte_seq_be().to_native(), p.1.1.to_byte_seq_be().to_native(), p.1.0.to_byte_seq_be().to_native()].concat();
    let mut tv = [0; 192];
    tv.copy_from_slice(&t[0..192]);
    let ph = ZKG2Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG2Affine::from(<ZKG2Projective as ZKHashToCurve<ZKExpandMsgXmd<ZKSha256>>>::hash_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g2_sswu_nu(msg : String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G2_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_encode_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let t = [p.0.1.to_byte_seq_be().to_native(), p.0.0.to_byte_seq_be().to_native(), p.1.1.to_byte_seq_be().to_native(), p.1.0.to_byte_seq_be().to_native()].concat();
    let mut tv = [0; 192];
    tv.copy_from_slice(&t[0..192]);
    let ph = ZKG2Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG2Affine::from(<ZKG2Projective as ZKHashToCurve<ZKExpandMsgXmd<ZKSha256>>>::encode_to_curve(msg, dst));
    ph == q
}