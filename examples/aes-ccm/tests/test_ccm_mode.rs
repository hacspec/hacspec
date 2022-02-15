use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;
use hacspec_aes::*;
use hacspec_aes_ccm::*;

// These tests have been taken from pages 23-24 of https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38c.pdf
// alen, nlen, plen, tlen are the octet (byte = 8 bit) lengths of the sequences and not the bit lengths

#[test]
fn kat_aes_ccm_1() {
    let ad = ByteSeq::from_public_slice(&[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    let n = ByteSeq::from_public_slice(&[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16]);
    let pay = ByteSeq::from_public_slice(&[0x20, 0x21, 0x22, 0x23]);


    let key = Key128::from_public_slice(&[
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f
    ]);

    let expected_ct = ByteSeq::from_public_slice(&[
        0x71, 0x62, 0x01, 0x5b, 0x4d, 0xac, 0x25, 0x5d
    ]);

    let ad2 = ad.clone();
    let n2 = n.clone();
    let pay2 = pay.clone();
    let clen = expected_ct.len();
    let tlen: usize = 4;

    let out_ct = encrypt_ccm(ad, n, pay, key, tlen);
    assert_eq!(expected_ct, out_ct);

    let out_pay = decrypt_ccm(ad2, n2, key, out_ct, clen, tlen);
    assert_eq!(pay2, out_pay.unwrap());
}

#[test]
fn kat_aes_ccm_2() {
    let n = ByteSeq::from_public_slice(&[0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17]);
    let ad = ByteSeq::from_public_slice(&[
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f
    ]);
    let pay = ByteSeq::from_public_slice(&[
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
        0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f
    ]);

    let key = Key128::from_public_slice(&[
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f
    ]);

    let expected_ct = ByteSeq::from_public_slice(&[
        0xd2, 0xa1, 0xf0, 0xe0, 0x51, 0xea, 0x5f, 0x62,
        0x08, 0x1a, 0x77, 0x92, 0x07, 0x3d, 0x59, 0x3d,
        0x1f, 0xc6, 0x4f, 0xbf, 0xac, 0xcd
    ]);

    let n2 = n.clone();
    let ad2 = ad.clone();
    let pay2 = pay.clone();
    let clen = expected_ct.len();
    let tlen: usize = 6;

    let out_ct = encrypt_ccm(ad, n, pay, key, tlen);
    assert_eq!(expected_ct, out_ct);

    let out_pay = decrypt_ccm(ad2, n2, key, out_ct, clen, tlen);
    assert_eq!(pay2, out_pay.unwrap());
}

#[test]
fn kat_aes_ccm_3() {
    let ad = ByteSeq::from_public_slice(&[
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13
    ]);
    let n = ByteSeq::from_public_slice(&[
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b
    ]);
    let pay = ByteSeq::from_public_slice(&[
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
        0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
        0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37
    ]);

    let key = Key128::from_public_slice(&[
        0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
        0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f
    ]);

    let expected_ct = ByteSeq::from_public_slice(&[
        0xe3, 0xb2, 0x01, 0xa9, 0xf5, 0xb7, 0x1a, 0x7a,
        0x9b, 0x1c, 0xea, 0xec, 0xcd, 0x97, 0xe7, 0x0b,
        0x61, 0x76, 0xaa, 0xd9, 0xa4, 0x42, 0x8a, 0xa5,
        0x48, 0x43, 0x92, 0xfb, 0xc1, 0xb0, 0x99, 0x51
    ]);

    let ad2 = ad.clone();
    let n2 = n.clone();
    let pay2 = pay.clone();
    let clen = expected_ct.len();
    let tlen: usize = 8;

    let out_ct = encrypt_ccm(ad, n, pay, key, tlen);
    assert_eq!(expected_ct, out_ct);

    let out_pay = decrypt_ccm(ad2, n2, key, out_ct, clen, tlen);
    assert_eq!(pay2.clone(), out_pay.unwrap());
}

create_test_vectors!(
    AesCcmTestVector,
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
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
    let tests: AesCcmTestVector = AesCcmTestVector::from_file("tests/aes_ccm_test_wycheproof.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "AES-CCM" => (),
        _ => panic!("This is not an AES-CCM test vector."),
    };

    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "AeadTest");
        if testGroup.keySize != 128 {
            // not implemented
            println!("Only AES 128 is implemented.");
            skipped_tests += testGroup.tests.len();
            continue;
        };
        if testGroup.tagSize < 32 {
            println!("MAC lengths < 32 are not allowed for AES CCM.");
            skipped_tests += testGroup.tests.len();
            continue;
        }
        for test in testGroup.tests.iter() {
            let valid = test.result.eq("valid");
            println!("Test {:?}: {:?}", test.tcId, test.comment);

            let n = ByteSeq::from_hex(&test.iv);
            let pay = ByteSeq::from_hex(&test.msg); // payload
            let ad = ByteSeq::from_hex(&test.aad); // adata
            let cipher_hex = format!("{}{}", test.ct, test.tag);
            let exp_cipher = ByteSeq::from_hex(&cipher_hex);
            let k = Key128::from_hex(&test.key);

            let pay2 = pay.clone();
            let ad2 = ad.clone();
            let n2 = n.clone();
            let tlen = testGroup.tagSize / 8;
            let clen = exp_cipher.len();

            if valid {
                let cipher = encrypt_ccm(ad, n, pay, k, tlen);
                assert_eq!(cipher, exp_cipher);

                if !test.ct.eq("") {
                    let p = decrypt_ccm(ad2, n2, k, cipher, clen, tlen);
                    assert_eq!(pay2, p.unwrap());
                }
            }

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
