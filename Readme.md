# hacspec

A new specification language for crypto primitives in Rust.

*This is the successor of https://github.com/HACS-workshop/hacspec.*

Documentation and API reference can be found [here](https://hacspec.github.io/hacspec/).

A formal description of the hacspec language can be found in [Language.md](Language.md)

# Repository Structure

This is a cargo workspace consisting of three crates:
* [hacspec](hacspec/)
* [abstract-integers](abstract-integers/)
* [secret-integers](secret-integers/)

# Examples
There's a set of example specs [here](hacspec/examples/).
To run all examples one can either use `cargo test --example <name>` or the helper script `test-examples.sh` to run all examples.

* [AES 128](hacspec/examples/aes/aes.rs)
* [Chacha20](hacspec/examples/chacha/chacha20.rs)
* [Poly1305](hacspec/examples/chacha/poly1305.rs)
* [Chacha20Poly1305](hacspec/examples/chacha/chacha20poly1305.rs)
