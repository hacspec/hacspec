# hacspec ![crate][crate-outdated-image] [![Docs][docs-master-image]][docs-master-link] [![Build & Test Status][build-image]][build-link] [![Docs Status][deploy-docs-image]][deploy-docs-link] ![Maturity Level][maturitylevel-image]

A new specification language for crypto primitives in Rust.

*This is the successor of https://github.com/HACS-workshop/hacspec.*

A formal description of the hacspec language can be found in [Language.md](Language.md)

# Repository Structure

This is a cargo workspace consisting of five main crates:
* [hacspec](hacspec/)
* [abstract-integers](abstract-integers/)
* [secret-integers](secret-integers/)
* [hacspec-dev](hacspec-dev/)
* [hacspec-examples](spec-examples/)

There's an additional crate [hacspec-attributes](attributes) that is only used in the hacspec library.

The clippy checker for the hacspec language lives in a [separate repository](https://github.com/hacspec/rust-clippy/tree/hacspec).

# Examples
There's a set of example specs [here](spec-examples/).
To run all examples one can either use `cargo test`.

* [AES 128/256](hacspec/spec-examples/aes-gcm/aes.rs)
* [GF 128](hacspec/spec-examples/aes-gcm/gf128.rs)
* [AES-GCM 128/256](hacspec/spec-examples/aes-gcm/aesgcm.rs)
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

[//]: # (badges)

[crate-outdated-image]: https://img.shields.io/badge/crate-outdated-red.svg
[crate-image]: https://img.shields.io/crates/v/hacspec.svg
[crate-link]: https://crates.io/crates/hacspec
[docs-master-image]: https://img.shields.io/badge/docs-master-blue.svg
[docs-master-link]: https://hacspec.github.io/hacspec/hacspec/index.html
[docs-image]: https://docs.rs/hacspec/badge.svg
[docs-link]: https://docs.rs/hacspec/
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[build-image]: https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg?branch=master&event=push
[build-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Build+%26+Test%22
[deploy-docs-image]: https://github.com/hacspec/hacspec/workflows/Deploy%20Docs/badge.svg?branch=master&event=push
[deploy-docs-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Deploy+Docs%22
[maturitylevel-image]: https://img.shields.io/badge/maturity-alpha-red.svg
