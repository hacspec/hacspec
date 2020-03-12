use hacspec::prelude::*;

#[test]
fn test_create_test_vectors() {
    create_test_vectors!(
        MyTestVectors,
        info: String,
        tests: Vec<MyTestVector>
    );
    create_test_vectors!(
        MyTestVector,
        x: u32,
        s: String
    );

    let tests = MyTestVectors::new("tests/sample_test_vector.json");
    
    assert_eq!(tests.info, "Some info text etc.");

    let expected_x = [5u32, 42];
    for (test, &expected) in tests.tests.iter().zip(&expected_x) {
        assert_eq!(test.x, expected);
    }
    let expected_s = ["lalalala", "blabla"];
    for (test, &expected) in tests.tests.iter().zip(&expected_s) {
        assert_eq!(test.s, expected);
    }
}
