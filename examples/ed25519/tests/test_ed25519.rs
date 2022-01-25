use hacspec_ed25519::*;
//use hacspec_curve25519::*;
use hacspec_dev::prelude::*;
use hacspec_lib::*;
//use curve25519_dalek::{scalar::Scalar, edwards::CompressedEdwardsY};
//use ed25519_dalek::Sha512;

create_test_vectors!(
    Ed25519TestVector,
    message: String,
    pub_key: String,
    signature: String
);

#[test]
fn test_vectors() {
    let v: Vec<Ed25519TestVector> = Ed25519TestVector::from_file("tests/cases.json");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
    }
}

/*
#[test]
fn printer() {
    let l = Ed25519FieldElement::ZERO()
        - (Ed25519FieldElement::from_literal(121665u128)
            * Ed25519FieldElement::from_literal(121666u128).inv());
    let l = l.to_byte_seq_le().to_native();
    print!("[");
    for t in l {
        print!("0x{:02x?}u8, ", t);
    }
    print!("]");
    assert!(false);
}
*/