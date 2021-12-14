use hacspec_lib::*;
use hacspec_bls12_381_hash::*;
use h2c_rust_ref::*;
use redox_ecc::ellipticcurve::EllipticCurve;
use redox_ecc::ops::FromFactory;


//use amcl::bls381::bls381::core::*;
use pairing_plus::hash_to_curve::HashToCurve;
use pairing_plus::bls12_381::{G1, Fq};
use pairing_plus::hash_to_field::{ExpandMsgXmd, BaseFromRO};
use sha2::Sha256;
use pairing_plus::{CurveProjective, CurveAffine};

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;


#[test]
fn it_works() {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg = b"hello world";
    let a = <G1 as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve::<&[u8], &[u8]>(msg, dst).into_affine();
    let p = g1_hash_to_curve_sswu(&ByteSeq::from_public_slice(msg), &ByteSeq::from_public_slice(dst));
    let x = a.as_tuple().0.to_string();
    println!("x: {}\ny: {}", x, a.as_tuple().1);
    println!("x: {}\ny: {}", p.0.to_byte_seq_be().to_hex(), p.1.to_byte_seq_be().to_hex());
    assert!(false);

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