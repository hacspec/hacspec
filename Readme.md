# hacspec ![crate][crate-outdated-image] [![Docs][docs-master-image]][docs-master-link] [![Build & Test Status][build-image]][build-link] [![Docs Status][deploy-docs-image]][deploy-docs-link] ![Maturity Level][maturitylevel-image]

A new specification language for crypto primitives in Rust.

*This is the successor of https://github.com/HACS-workshop/hacspec.*

A formal description of the hacspec language can be found in [Language.md](Language.md)

# Repository Structure

This is a cargo workspace consisting of six main crates:
* [hacspec](hacspec/): the compiler, typechecker and language infrastructure for the hacspec subset of Rust
* [hacspec-lib](hacspec-lib):  the standard library of hacspec programs
* [abstract-integers](abstract-integers/): wrapper around `BigInt` for modular natural integers
* [secret-integers](secret-integers/): wrapper around integer types for constant-timedness
* [unsafe-hacspec-examples](unsafe-hacspec-examples/): cryptographic specs written in hacspec but not formally typechecked yet(hence the unsafety) as hacspec is a work in progress

The [hacspec-examples](hacspec_examples/) folder contains 
cryptographic primitives that have passed the hacspec typechecking.

There's an additional crate [hacspec-attributes](attributes) that is
only used in the hacspec library, and [hacspec-dev](hacspec-dev/)
which are hacspec utilities that are not part of the language.

Finally, the [hacspec-fstar](hacspec-fstar/) folder contains F* translations
of the cryptograpghic specs, produced by the hacspec compiler.

# Examples

There's a set of example specs, divided between the [safe](hacspec-examples/) and [unsafe](unsafe-hacspec-examples). To run all examples one can use `cargo test`.

## Safe examples

* [Chacha20](hacspec-examples/hacspec-chacha20/src/chacha20.rs)
* [Poly1305](hacspec-examples/hacspec-poly1305/src/poly1305.rs)
* [Chacha20Poly1305](hacspec-examples/hacspec-chacha20poly1305/src/chacha20poly1305.rs)

## Unsafe examples

* [AES 128/256](unsafe-hacspec-examples/src/aes_gcm/aes.rs)
* [GF 128](unsafe-hacspec-examples/src/aes_gcm/gf128.rs)
* [AES-GCM 128/256](unsafe-hacspec-examples/src/aes_gcm/aesgcm.rs)
* [Blake2b](unsafe-hacspec-examples/src/blake2/blake2b.rs)
* [Curve25519](unsafe-hacspec-examples/src/curve25519/curve25519.rs)
* [Fips202](unsafe-hacspec-examples/src/fips202/fips202.rs)
* [SHA256](unsafe-hacspec-examples/src/sha2/sha2.rs)
* [HKDF-SHA256](unsafe-hacspec-examples/src/hkdf/hkdf.rs)
* [HMAC-SHA256](unsafe-hacspec-examples/src/hmac/hmac.rs)
* [P256](unsafe-hacspec-examples/src/p256/p256.rs)
* [NTRU-prime](unsafe-hacspec-examples/src/ntru_prime/ntru_prime.rs)

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

# The hacspec language infrastructure

The language infrastructure is excluded from the main workspace of crates, 
so it won't be build when you launch `cargo build` from the
root of the repository.

Please refer to the [dedicated README.md](hacspec/README.md) 
for instructions about how to run the typechecker and compiler. 