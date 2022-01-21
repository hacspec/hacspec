use hacspec_ed25519::*;
//use hacspec_curve25519::*;
use hacspec_lib::*;
//use curve25519_dalek::{scalar::Scalar, edwards::CompressedEdwardsY};
//use ed25519_dalek::Sha512;

#[test]
fn test_test() {
    let s1 = Scalar::from_literal(63);
    let s2 = sc_to_sc_modl(s1);
    let s3 = ScalarModL::from_literal(63);
    let s4 = sc_modl_to_sc(s3);
    println!("{}", s1.to_byte_seq_le().to_hex());
    println!("{}", s2.to_byte_seq_le().to_hex());
    println!("{}", s3.to_byte_seq_le().to_hex());
    println!("{}", s4.to_byte_seq_le().to_hex());
    assert!(false);

}

#[test]
fn test_secret_to_public() {
    let s = SerializedScalar::from_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
    let result = CompressedEdPoint::from_hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
    let a = secret_to_public(s);
    assert_bytes_eq!(a, result);

    let s = SerializedScalar::from_hex("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb");
    let result = CompressedEdPoint::from_hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c");
    let a = secret_to_public(s);
    assert_bytes_eq!(a, result);
}

#[test]
fn test_sign() {
    let s = SerializedScalar::from_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
    let msg = ByteSeq::from_public_slice(b"");
    let sig = sign(s, &msg);
    let result = Signature::from_hex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
        5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
    assert_bytes_eq!(sig, result);
}

