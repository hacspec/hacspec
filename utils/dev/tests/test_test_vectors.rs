use hacspec_dev::prelude::*;

#[test]
fn test_read_test_vectors() {
    create_test_vectors!(MyTestVectors, info: String, tests: Vec<MyTestVector>);
    create_test_vectors!(MyTestVector, x: u32, s: String);

    let tests: MyTestVectors = MyTestVectors::from_file("tests/sample_test_vector.json");

    assert_eq!(tests.info, "Some info text etc.");

    let expected_x = [5u32, 42];
    for (test, &expected) in tests.tests.iter().zip(&expected_x) {
        assert_eq!(test.x, expected);
    }
    let expected_s = ["lalalala", "blabla"];
    for (test, &expected) in tests.tests.iter().zip(&expected_s) {
        assert_eq!(test.s, expected);
    }

    tests.write_file("tests/sample_test_vector_out.json");
}

#[test]
fn test_write_test_vectors() {
    create_test_vectors!(
        MyTestVectors,
        info: String,
        version: u32,
        tests: Vec<MyTestVector>
    );
    create_test_vectors!(MyTestVector, x: u32, s: String, d: String);

    fn generate_test() -> MyTestVector {
        MyTestVector {
            x: 1,
            s: "Test1".to_string(),
            d: "deadbeef".to_string(),
        }
    }

    fn generate_test_vecs() -> MyTestVectors {
        let tests = vec![generate_test()];
        MyTestVectors {
            info: "Test Vectors for Testing".to_string(),
            version: 1,
            tests: tests,
        }
    }

    let test_vecs = generate_test_vecs();
    test_vecs.write_file("tests/test_vector_write.json");
}
