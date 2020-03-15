use hacspec::prelude::*;

use crate::{aes, aesgcm::*, gf128};

struct AeadTestVector<'a> {
    key: &'a str,
    nonce: &'a str,
    msg: &'a str,
    aad: &'a str,
    exp_cipher: &'a str,
    exp_mac: &'a str,
}

const KAT: [AeadTestVector; 4] = [
    AeadTestVector {
        key: "00000000000000000000000000000000",
        nonce: "000000000000000000000000",
        msg: "",
        aad: "",
        exp_cipher: "",
        exp_mac: "58e2fccefa7e3061367f1d57a4e7455a"
    },
    AeadTestVector {
        key	: "00000000000000000000000000000000",
        nonce	: "000000000000000000000000",
        aad	: "",
        msg	: "00000000000000000000000000000000",
        exp_cipher : "0388dace60b6a392f328c2b971b2fe78",
        exp_mac	: "ab6e47d42cec13bdf53a67b21257bddf",
    },
    AeadTestVector {
        key	: "feffe9928665731c6d6a8f9467308308",
        nonce	: "cafebabefacedbaddecaf888",
        msg	: "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
        aad	: "",
        exp_cipher : "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985",
        exp_mac	: "4d5c2af327cd64a62cf35abd2ba6fab4",
    },
    AeadTestVector {
        key	: "feffe9928665731c6d6a8f9467308308",
        nonce	: "cafebabefacedbaddecaf888",
        msg	: "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
        aad	: "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        exp_cipher: "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
        exp_mac	: "5bc94fbc3221a5db94fae95ae7121a47",
    }
];

#[test]
fn kat_test() {
    for kat in KAT.iter() {
        let k = aes::Key::from(kat.key);
        let nonce = aes::Nonce::from(kat.nonce);
        let exp_mac = gf128::Tag::from(kat.exp_mac);
        let msg = ByteSeq::from(kat.msg);
        let aad = ByteSeq::from(kat.aad);
        let exp_cipher = ByteSeq::from(kat.exp_cipher);

        let (cipher, mac) = encrypt(k, nonce, aad.clone(), msg.clone());
        assert_eq!(
            exp_cipher
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>(),
            cipher
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            exp_mac
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>(),
            mac.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
        );

        let decrypted_msg = decrypt(k, nonce, aad, cipher, mac).unwrap();
        assert_eq!(
            msg.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
            decrypted_msg
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
    }
}
