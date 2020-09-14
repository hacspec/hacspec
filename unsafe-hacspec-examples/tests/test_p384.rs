use unsafe_hacspec_examples::ec::{p384::*, Affine};

use hacspec_dev::prelude::*;

// TODO: this is duplicating a lot of code from test_p256!
create_test_vectors!(
    P384TestVector,
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
    let tests: P384TestVector = P384TestVector::from_file("tests/ecdh_secp384r1_ecpoint_test.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "ECDH" => (),
        _ => panic!("This is not an ECDH test vector."),
    };
    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "EcdhEcpointTest");
        assert_eq!(testGroup.curve, "secp384r1");
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
            // println!("k: {:?}", k);
            let p = Affine(
                FieldElement::from_hex(&test.public[2..98]),
                FieldElement::from_hex(&test.public[98..]),
            );
            // println!("p: {:?}", p);
            let expected = FieldElement::from_hex(&test.shared);
            // println!("expected: {:?}", expected);
            let shared = point_mul(k, p);
            // println!("computed: {:?}", shared);
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
