use hacspec_dev::prelude::*;
use hacspec_ed25519::*;
use hacspec_lib::*;

create_test_vectors!(
    Ed25519TestVector,
    message: String,
    pub_key: String,
    signature: String
);

create_test_vectors!(MoreTestVec, pub_key: String, signature: String);

// Testing test vectors from https://github.com/novifinancial/ed25519-speccheck
#[test]
fn test_vectors_zcash() {
    let v: Vec<Ed25519TestVector> = Ed25519TestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3, 4, 5, 9, 10, 11];
    println!("Zcash spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = zcash_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_ieft_cofactored() {
    let v: Vec<Ed25519TestVector> = Ed25519TestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3, 4, 5];
    println!("ietf cofactored spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = ietf_cofactored_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_ieft_cofactorless() {
    let v: Vec<Ed25519TestVector> = Ed25519TestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3];
    println!("ietf cofactorless spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = ietf_cofactorless_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_alg2() {
    let v: Vec<Ed25519TestVector> = Ed25519TestVector::from_file("tests/cases.json");
    let expected_success = [2, 3, 4, 5];
    println!("ietf cofactored spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = alg2_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

// There are 14 points of small order, 6 of which are not on canonical form
// morecases contains contains test vectors where R and A are every combination of these small order points
// Zcash verifies every test as it allows non-canonical encodings
// Alg2 rejects every test as it doesn't allow small order points
// ietf_cofactored verifies all canonical encoded tests
// ietf_cofactorless verifes only when the equation coincidentally holds
#[test]
fn test_more_vector() {
    let msg = ByteSeq::from_public_slice(b"Zcash");
    let v: Vec<MoreTestVec> = MoreTestVec::from_file("tests/morecases.json");
    println!("Differences on more test vectors");
    for i in 0..v.len() {
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result_zcash = zcash_verify(pub_key, signature, &msg);
        let result_ietf_cofactored = ietf_cofactored_verify(pub_key, signature, &msg);
        let result_ietf_cofactorless = ietf_cofactorless_verify(pub_key, signature, &msg);
        let result_alg2 = alg2_verify(pub_key, signature, &msg);
        println!(
            "Diffenrence in test {}: zcash: {:?}, ietf_cf: {:?}, ietf_cl: {:?}, alg2: {:?}",
            i, result_zcash, result_ietf_cofactored, result_ietf_cofactorless, result_alg2
        );
    }
}
