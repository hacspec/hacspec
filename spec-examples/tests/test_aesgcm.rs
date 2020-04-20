use hacspec::prelude::*;

use hacspec_examples::aes_gcm::*;

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

const KAT_256: [AeadTestVector; 2] = [
    AeadTestVector {
        key: "E3C08A8F06C6E3AD95A70557B23F75483CE33021A9C72B7025666204C69C0B72",
        nonce: "12153524C0895E81B2C28465",
        msg: "",
        aad: "D609B1F056637A0D46DF998D88E5222AB2C2846512153524C0895E8108000F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F30313233340001",
        exp_cipher: "",
        exp_mac: "2F0BC5AF409E06D609EA8B7D0FA5EA50"
    },
    AeadTestVector {
        key: "E3C08A8F06C6E3AD95A70557B23F75483CE33021A9C72B7025666204C69C0B72",
        nonce: "12153524C0895E81B2C28465",
        msg: "08000F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A0002",
        aad: "D609B1F056637A0D46DF998D88E52E00B2C2846512153524C0895E81",
        exp_cipher: "E2006EB42F5277022D9B19925BC419D7A592666C925FE2EF718EB4E308EFEAA7C5273B394118860A5BE2A97F56AB7836",
        exp_mac: "5CA597CDBB3EDB8D1A1151EA0AF7B436"
    }
    ];

#[test]
fn kat_test() {
    for kat in KAT.iter() {
        let k = aes::Key128::from_hex(kat.key);
        let nonce = aes::Nonce::from_hex(kat.nonce);
        let exp_mac = gf128::Tag::from_hex(kat.exp_mac);
        let msg = ByteSeq::from_hex(kat.msg);
        let aad = ByteSeq::from_hex(kat.aad);
        let exp_cipher = ByteSeq::from_hex(kat.exp_cipher);

        let (cipher, mac) = encrypt_aes128(k, nonce, &aad, &msg);
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

        let decrypted_msg = decrypt_aes128(k, nonce, &aad, &cipher, mac).unwrap();
        assert_eq!(
            msg.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
            decrypted_msg
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
    }
}
#[test]
fn kat_test_256() {
    for kat in KAT_256.iter() {
        let k = aes::Key256::from_hex(kat.key);
        let nonce = aes::Nonce::from_hex(kat.nonce);
        let exp_mac = gf128::Tag::from_hex(kat.exp_mac);
        let msg = ByteSeq::from_hex(kat.msg);
        let aad = ByteSeq::from_hex(kat.aad);
        let exp_cipher = ByteSeq::from_hex(kat.exp_cipher);

        let (cipher, mac) = encrypt_aes256(k, nonce, &aad, &msg);
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

        let decrypted_msg = decrypt_aes256(k, nonce, &aad, &cipher, mac).unwrap();
        assert_eq!(
            msg.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
            decrypted_msg
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
    }
}
