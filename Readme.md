# hacspec

A new specification language for crypto primitives in Rust.

*This is the successor of https://github.com/HACS-workshop/hacspec.*

Documentation and API reference can be found [here](https://hacspec.github.io/hacspec/).

A formal description of the hacspec language can be found in [Language.md](Language.md)

# Repository Structure

This is a cargo workspace consisting of three crates:
* [hacspec](hacspec/) ![Build & Test](https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg) ![Deploy Docs](https://github.com/hacspec/hacspec/workflows/Deploy%20Docs/badge.svg)
* [abstract-integers](abstract-integers/)
* [secret-integers](secret-integers/)

The clippy checker for the hacspec language lives in a [separate repository](https://github.com/hacspec/rust-clippy/tree/hacspec)-

# Examples
There's a set of example specs [here](hacspec/spec-examples/).
To run all examples one can either use `cargo test`.

* [AES 128](hacspec/spec-examples/aes-gcm/aes.rs)
* [GF 128](hacspec/spec-examples/aes-gcm/gf128.rs)
* [AES-GCM 128](hacspec/spec-examples/aes-gcm/aesgcm.rs)
* [Chacha20](hacspec/spec-examples/chacha20-poly1305/chacha20.rs)
* [Poly1305](hacspec/spec-examples/chacha20-poly1305/poly1305.rs)
* [Chacha20Poly1305](hacspec/spec-examples/chacha20-poly1305/chacha20poly1305.rs)
* [Blake2b](hacspec/spec-examples/blake2/blake2b.rs)
* [Curve25519](hacspec/spec-examples/curve25519/curve25519.rs)
* [Fips202](hacspec/spec-examples/fips202/fips202.rs)
* [SHA256](hacspec/spec-examples/sha2/sha2.rs)
* [HKDF-SHA256](hacspec/spec-examples/hkdf/hkdf.rs)
* [HMAC-SHA256](hacspec/spec-examples/hkdf/hmac.rs)
* [P256](hacspec/spec-examples/p256/p256.rs)
