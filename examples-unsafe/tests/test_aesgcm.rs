use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use unsafe_hacspec_examples::aes_gcm::*;

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

macro_rules! to_public_vec {
    ($x:expr) => {
        $x.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    };
}

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

create_test_vectors!(
    AesGcmTestVector,
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    header: Vec<Value>,   // not used
    testGroups: Vec<TestGroup>
);

create_test_vectors!(
    TestGroup,
    ivSize: usize,
    keySize: usize,
    tagSize: usize,
    r#type: String,
    tests: Vec<Test>
);

create_test_vectors!(
    Test,
    tcId: usize,
    comment: String,
    key: String,
    iv: String,
    aad: String,
    msg: String,
    ct: String,
    tag: String,
    result: String,
    flags: Vec<String>
);

#[allow(non_snake_case)]
#[test]
fn test_wycheproof() {
    let tests: AesGcmTestVector = AesGcmTestVector::from_file("tests/aes_gcm_test_wycheproof.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "AES-GCM" => (),
        _ => panic!("This is not an AES-GCM test vector."),
    };
    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "AeadTest");
        let algorithm = match testGroup.keySize {
            128 => aes::AesVariant::Aes128,
            256 => aes::AesVariant::Aes256,
            _ => {
                // not implemented
                println!("Only AES 128 and 256 are implemented.");
                skipped_tests += testGroup.tests.len();
                continue;
            }
        };
        if testGroup.ivSize != 96 {
            // not implemented
            println!("Nonce sizes != 96 are not supported for AES GCM.");
            skipped_tests += testGroup.tests.len();
            continue;
        }
        for test in testGroup.tests.iter() {
            let valid = test.result.eq("valid");
            if test.comment == "invalid nonce size" {
                // not implemented
                println!("Invalid nonce sizes are not supported.");
                skipped_tests += 1;
                break;
            }
            println!("Test {:?}: {:?}", test.tcId, test.comment);
            let nonce = aes::Nonce::from_hex(&test.iv);
            let msg = ByteSeq::from_hex(&test.msg);
            let aad = ByteSeq::from_hex(&test.aad);
            let exp_cipher = ByteSeq::from_hex(&test.ct);
            let exp_tag = gf128::Tag::from_hex(&test.tag);
            let (cipher, tag) = match algorithm {
                aes::AesVariant::Aes128 => {
                    // let r = test_ring_aead(&key, &iv, &aad, &m, algorithm);
                    let k = aes::Key128::from_hex(&test.key);
                    encrypt_aes128(k, nonce, &aad, &msg)
                }
                aes::AesVariant::Aes256 => {
                    let k = aes::Key256::from_hex(&test.key);
                    encrypt_aes256(k, nonce, &aad, &msg)
                }
            };
            if valid {
                assert_eq!(to_public_vec!(tag), to_public_vec!(exp_tag));
            } else {
                assert_ne!(to_public_vec!(tag), to_public_vec!(exp_tag));
            }
            assert_eq!(to_public_vec!(cipher), to_public_vec!(exp_cipher));
            tests_run += 1;
        }
    }
    // Check that we ran all tests.
    println!(
        "Ran {} out of {} tests and skipped {}.",
        tests_run, num_tests, skipped_tests
    );
    assert_eq!(num_tests - skipped_tests, tests_run);
}

#[allow(non_snake_case)]
#[test]
fn generate_test_vectors() {
    const NUM_TESTS_EACH: usize = 100;
    let mut tests_128 = Vec::new();
    let mut tests_256 = Vec::new();

    for i in 0..NUM_TESTS_EACH {
        let msg_l = 123 + i;
        let aad_l = 13 + i;

        // Generate random key, nonce, message, and aad for AES 256.
        let k = aes::Key256::from_public_slice(&random_byte_vec(aes::Key256::length()));
        let nonce = aes::Nonce::from_public_slice(&random_byte_vec(aes::Nonce::length()));
        let msg = ByteSeq::from_public_slice(&random_byte_vec(msg_l));
        let aad = ByteSeq::from_public_slice(&random_byte_vec(aad_l));

        // Generate random key, nonce, message, and aad for AES 128.
        let k128 = aes::Key128::from_public_slice(&random_byte_vec(aes::Key128::length()));
        let nonce128 = aes::Nonce::from_public_slice(&random_byte_vec(aes::Nonce::length()));
        let msg128 = ByteSeq::from_public_slice(&random_byte_vec(msg_l));
        let aad128 = ByteSeq::from_public_slice(&random_byte_vec(aad_l));

        // Generate ciphertext and mac
        let (cipher, mac) = encrypt_aes256(k, nonce, &aad, &msg);
        let (cipher128, mac128) = encrypt_aes128(k128, nonce128, &aad128, &msg128);

        // self-test
        let decrypted_msg = decrypt_aes256(k, nonce, &aad, &cipher, mac).unwrap();
        assert_eq!(
            msg.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
            decrypted_msg
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
        let decrypted_msg128 = decrypt_aes128(k128, nonce128, &aad128, &cipher128, mac128).unwrap();
        assert_eq!(
            msg128
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>(),
            decrypted_msg128
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );

        // Store result.
        tests_256.push(Test {
            tcId: i,
            comment: String::default(),
            key: k.to_hex(),
            iv: nonce.to_hex(),
            aad: aad.to_hex(),
            msg: msg.to_hex(),
            ct: cipher.to_hex(),
            tag: mac.to_hex(),
            result: "valid".to_string(),
            flags: vec![],
        });
        tests_128.push(Test {
            tcId: i + NUM_TESTS_EACH,
            comment: String::default(),
            key: k128.to_hex(),
            iv: nonce128.to_hex(),
            aad: aad128.to_hex(),
            msg: msg128.to_hex(),
            ct: cipher128.to_hex(),
            tag: mac128.to_hex(),
            result: "valid".to_string(),
            flags: vec![],
        });
    }

    let test_group_256 = TestGroup {
        ivSize: aes::Nonce::length(),
        keySize: aes::Key256::length(),
        tagSize: gf128::Tag::length(),
        r#type: "AeadTest".to_string(),
        tests: tests_256,
    };
    let test_group_128 = TestGroup {
        ivSize: aes::Nonce::length(),
        keySize: aes::Key128::length(),
        tagSize: gf128::Tag::length(),
        r#type: "AeadTest".to_string(),
        tests: tests_128,
    };
    let test_vector = AesGcmTestVector {
        algorithm: "AES-GCM".to_string(),
        generatorVersion: "0.0.1".to_string(),
        numberOfTests: 1,
        notes: None,
        header: vec![],
        testGroups: vec![test_group_128, test_group_256],
    };

    // Write out test vectors.
    test_vector.write_file("tests/aes_gcm_test_vector_out.json");
}
