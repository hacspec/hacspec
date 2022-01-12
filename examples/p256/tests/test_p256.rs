use hacspec_lib::ByteSeq;
use hacspec_p256::*;

use hacspec_dev::prelude::*;

#[test]
fn test_p256_base() {
    let sk = P256Scalar::from_hex("14");
    let point_expected = (
        P256FieldElement::from_hex(
            "83A01A9378395BAB9BCD6A0AD03CC56D56E6B19250465A94A234DC4C6B28DA9A",
        ),
        P256FieldElement::from_hex(
            "76E49B6DE2F73234AE6A5EB9D612B75C9F2202BB6923F54FF8240AAA86F640B8",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk = P256Scalar::from_hex("018ebbb95eed0e13");
    let point_expected = (
        P256FieldElement::from_hex(
            "339150844EC15234807FE862A86BE77977DBFB3AE3D96F4C22795513AEAAB82F",
        ),
        P256FieldElement::from_hex(
            "B1C14DDFDC8EC1B2583F51E85A5EB3A155840F2034730E9B5ADA38B674336A21",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk =
        P256Scalar::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    let point_expected = (
        P256FieldElement::from_hex(
            "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
        ),
        P256FieldElement::from_hex(
            "B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);
}

create_test_vectors!(
    P256TestVector,
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    header: Vec<Value>,   // not used
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    schema: String,       // not used
    testGroups: Vec<TestGroup>
);

create_test_vectors!(
    TestGroup,
    curve: String,
    encoding: String,
    r#type: String,
    tests: Vec<Test>
);

create_test_vectors!(
    Test,
    tcId: usize,
    comment: String,
    public: String,
    private: String,
    shared: String,
    result: String,
    flags: Vec<String>
);

#[allow(non_snake_case)]
#[test]
fn test_wycheproof_plain() {
    let tests: P256TestVector = P256TestVector::from_file("tests/ecdh_secp256r1_ecpoint_test.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "ECDH" => (),
        _ => panic!("This is not an ECDH test vector."),
    };
    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "EcdhEcpointTest");
        assert_eq!(testGroup.curve, "secp256r1");
        assert_eq!(testGroup.encoding, "ecpoint");
        for test in testGroup.tests.iter() {
            println!("Test {:?}: {:?}", test.tcId, test.comment);
            if !test.result.eq("valid")
                && !(test.result.eq("invalid") && test.comment.eq("point is not on curve"))
            {
                println!("We're only doing valid tests for now.");
                skipped_tests += 1;
                continue;
            }
            let not_on_curve =
                test.result.eq("invalid") && test.comment.eq("point is not on curve");
            if test.comment == "compressed public key" {
                // not implemented
                println!("Compressed public keys are not supported.");
                skipped_tests += 1;
                continue;
            }
            assert_eq!(&test.public[0..2], "04");
            let k = P256Scalar::from_hex(&test.private);
            let p = (
                P256FieldElement::from_hex(&test.public[2..66]),
                P256FieldElement::from_hex(&test.public[66..]),
            );
            if not_on_curve {
                assert!(!p256_validate_public_key(p));
                tests_run += 1;
                continue;
            }
            assert!(p256_validate_public_key(p));
            let expected = P256FieldElement::from_hex(&test.shared);
            let shared = match p256_point_mul(k, p) {
                Ok(s) => s,
                Err(_) => panic!("Unexpected error in point_mul"),
            };
            assert_eq!(shared.0, expected);
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

#[test]
fn invalid_scalars() {
    let zero = ByteSeq::from_hex("00");
    assert!(!p256_validate_private_key(&zero));

    let too_large =
        ByteSeq::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    assert!(!p256_validate_private_key(&too_large));

    let largest_valid =
        ByteSeq::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    assert!(p256_validate_private_key(&largest_valid));
}

#[test]
fn point_validation() {
    let not_on_curve = (
        P256FieldElement::from_hex(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        ),
        P256FieldElement::from_hex(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));

    let valid_point = (
        P256FieldElement::from_hex(
            "31028f3377fc8f2b1967edaab90213acad0da9f50897f08f57537f78f1167447",
        ),
        P256FieldElement::from_hex(
            "43a1930189363bbde2ac4cbd1649cdc6f451add71dd2f16a8a867f2b17caa16b",
        ),
    );
    assert!(p256_validate_public_key(valid_point));

    let not_on_curve = (
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));

    let not_on_curve = (
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000001",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));
}
