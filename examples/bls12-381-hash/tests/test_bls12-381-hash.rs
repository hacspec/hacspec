use hacspec_bls12_381::*;
use hacspec_bls12_381_hash::*;
use hacspec_lib::*;
//use hacspec_sha256::*;

#[test]
fn test_g1_hash_to_curve() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SVDW_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_hash_to_curve(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_hash_to_curve(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_hash_to_curve(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g1_encode_to_curve() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SVDW_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_encode_to_curve(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_encode_to_curve(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_encode_to_curve(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_hash_to_curve() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SVDW_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_hash_to_curve(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_hash_to_curve(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_hash_to_curve(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_encode_to_curve() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SVDW_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_encode_to_curve(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); //r
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_encode_to_curve(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_encode_to_curve(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}
