use hacspec_lib::*;
use hacspec_ed25519::*;
use ed25519_dalek::{SecretKey as DSecretKey, ExpandedSecretKey, PublicKey as DPublicKey, Signature as DSignature, Verifier};
use ed25519_zebra::SigningKey;

extern crate quickcheck;
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[quickcheck]
fn test_sign_dalek(sk: (u128, u128), msg: String) -> bool {
    let (sk1, sk2) = sk;
    let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
    let sk_hac = SecretKey::from_public_slice(&sk);
    let msg_hac = &ByteSeq::from_public_slice(msg.as_bytes());
    let sig_hac = sign(sk_hac, &msg_hac);

    let sk_dal = DSecretKey::from_bytes(&sk).unwrap();
    let key_dal = ExpandedSecretKey::from(&sk_dal);
    let sig_dal = key_dal.sign(msg.as_bytes(), &DPublicKey::from(&sk_dal));


    sig_dal.to_bytes().to_vec() == sig_hac.to_le_bytes().to_native()
}

#[quickcheck]
fn test_sign_zebra(sk: (u128, u128), msg: String) -> bool {
    let (sk1, sk2) = sk;
    let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
    let sk_hac = SecretKey::from_public_slice(&sk);
    let msg_hac = &ByteSeq::from_public_slice(msg.as_bytes());
    let sig_hac = sign(sk_hac, &msg_hac);

    let sk: &[u8] = &sk;
    let sk_zeb = SigningKey::try_from(sk).unwrap();
    let sig_zeb = sk_zeb.sign(msg.as_bytes());

    <[u8; 64]>::from(sig_zeb).to_vec() == sig_hac.to_le_bytes().to_native()
}

#[test]
fn test_dalek_disagrees() {
    let msg = "39a591f5321bbe07fd5a23dc2f39d025d74526615746727ceefd6e82ae65c06f";
    let pk = "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let sig = "a9d55260f765261eb9b84e106f665e00b867287a761990d7135963ee0a7d59dca5bb704786be79fc476f91d3f3f89b03984d8068dcf1bb7dfc6637b45450ac04";

    let msg_hac = ByteSeq::from_hex(msg);
    let pk_hac = PublicKey::from_hex(pk);
    let sig_hac = Signature::from_hex(sig);
    let result_hac = ietf_cofactorless_verify(pk_hac, sig_hac, &msg_hac);

    let msg_dal = msg_hac.to_native();
    let pk_dal = DPublicKey::from_bytes(&pk_hac.to_le_bytes().to_native()).unwrap();
    let sig_dal = DSignature::from_bytes(&sig_hac.to_le_bytes().to_native()).unwrap();
    let result_dal = pk_dal.verify(&msg_dal, &sig_dal);

    assert!(result_hac.is_err());
    assert!(result_dal.is_ok());
}