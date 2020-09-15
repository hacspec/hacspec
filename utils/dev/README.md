# hacspec dev-lib
This crate contains functionality that can be useful when implementing hacspecs.
These MUST NOT be used in specs but can be useful in tests.

## Using test vectors
To parse JSON test vectors this crate provides the `create_test_vectors!` macro
that allows for convenient usage of the SERDE JSON interface.
This is commonly used as follows

```Rust
// The vector of tests with some additional information.
create_test_vectors!(
    MyTestVectors,
    info: String,
    tests: Vec<MyTestVector>
);

// A test.
create_test_vectors!(
    MyTestVector,
    x: u32,
    s: String
);

// Now we can read the JSON file into MyTestVectors
let tests = MyTestVectors::from_file("test_vector.json");

// We can also write the test vectors to a JSON file.
tests.write_file("test_vector_out.json");
```
