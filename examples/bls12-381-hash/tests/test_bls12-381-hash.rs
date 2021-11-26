use hacspec_bls12_381_hash::*;
use hacspec_bls12_381::*;
use hacspec_lib::*;
//use hacspec_sha256::*;



#[test]
fn test_expand_message() {
    let msg = ByteSeq::from_public_slice(b"hello_world");
    let dst = ByteSeq::from_public_slice(b"hacspec_dst"); 
    let len_in_bytes = 64;
    let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
    let result = ByteSeq::from_hex("ffe3dc533040dcffab4967f737e56c80ffaeba9c76b66f3bdc66de805a1b2211672d5c4ec5e4d18ca6284e9464e2b2db8595f19190f2c96dcfcbf357a972e4c4");
    assert_eq!(expm.len(), len_in_bytes);
    assert_eq!(expm.to_hex(), result.to_hex());
}

#[test]
fn test_fp_hash_to_field() {
    let msg = ByteSeq::from_public_slice(b"hello_world");
    let count = 2;
    let fps = fp_hash_to_field(&msg, count);
    assert_eq!(fps[0], Fp::ZERO());
}

#[test]
fn test_fp2_hash_to_field() {
    let msg = ByteSeq::from_public_slice(b"hello_world");
    let count = 2;
    let fps = fp2_hash_to_field(&msg, count);
    assert_eq!(fps[0], fp2zero());
}