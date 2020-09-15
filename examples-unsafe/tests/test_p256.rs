use unsafe_hacspec_examples::ec::{p256::*, Affine};

use hacspec_dev::prelude::*;

#[test]
fn test_p256_base() {
    let sk = Scalar::from_hex("14");
    let point_expected = (
        FieldElement::from_hex("83A01A9378395BAB9BCD6A0AD03CC56D56E6B19250465A94A234DC4C6B28DA9A"),
        FieldElement::from_hex("76E49B6DE2F73234AE6A5EB9D612B75C9F2202BB6923F54FF8240AAA86F640B8"),
    );

    let point_computed = point_mul_base(sk);
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk = Scalar::from_hex("018ebbb95eed0e13");
    let point_expected = (
        FieldElement::from_hex("339150844EC15234807FE862A86BE77977DBFB3AE3D96F4C22795513AEAAB82F"),
        FieldElement::from_hex("B1C14DDFDC8EC1B2583F51E85A5EB3A155840F2034730E9B5ADA38B674336A21"),
    );

    let point_computed = point_mul_base(sk);
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk = Scalar::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    let point_expected = (
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        FieldElement::from_hex("B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A"),
    );

    let point_computed = point_mul_base(sk);
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
            if !test.result.eq("valid") {
                println!("We're only doing valid tests for now.");
                skipped_tests += 1;
                continue;
            }
            if test.comment == "compressed public key" {
                // not implemented
                println!("Compressed public keys are not supported.");
                skipped_tests += 1;
                continue;
            }
            assert_eq!(&test.public[0..2], "04");
            let k = Scalar::from_hex(&test.private);
            let p = Affine(
                FieldElement::from_hex(&test.public[2..66]),
                FieldElement::from_hex(&test.public[66..]),
            );
            let expected = FieldElement::from_hex(&test.shared);
            let shared = point_mul(k, p);
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
