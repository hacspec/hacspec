# hacspec [![hacspec chat][chat-image]][chat-link]

A specification language for crypto primitives in Rust.

*This is the successor of https://github.com/HACS-workshop/hacspec.*

## Crates

| Name             | Crates.io                                                                 |                                                                 Docs                                                                  |                        CI                         |
| :--------------- | :------------------------------------------------------------------------ | :-----------------------------------------------------------------------------------------------------------------------------------: | :-----------------------------------------------: |
| hacspec          | [![crates.io][crate-hacspec]](https://crates.io/crates/hacspec)           |     [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](language/)      | [![Build & Test Status][build-image]][build-link] |
| hacspec-lib      | [![crates.io][crate-lib]](https://crates.io/crates/hacspec-lib)           |   [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_lib/index.html)    | [![Build & Test Status][build-image]][build-link] |
| hacspec-provider | [![crates.io][crate-provider]](https://crates.io/crates/hacspec-provider) | [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_provider/index.html) | [![Build & Test Status][build-image]][build-link] |

## Usage

### Writing hacspec
hacspec is always valid Rust code such that starting to write hacspec is as simple as writing Rust code that is compliant with the [language](Language.md) specification.
However, this is very tedious.
It is recommended to use the [hacspec standard library](https://crates.io/crates/hacspec-lib) to write hacspec.
In order to ensure that the code is a hacspec one can use the typecheker.

### Typechecking
First ensure that Rust nightly is installed and the typechecker is installed.

```bash
rustup toolchain install nightly
rustup component add --toolchain nightly rustc-dev
cargo +nightly install hacspec
```

In a hacspec crate or workspace directory typechecking can be done as follows now:

```bash
cargo +nightly hacspec <crate-name>
```

Note that the crate needs to be compiled before it can be typechecked.

```bash
cargo +nightly build
```

If typechecking succeeds, it should show

```bash
> Successfully verified.
```

### Generating code
To generate F* or EasyCrypt code from hacspec the typechecker (see above) is required.

```bash
cargo +nightly hacspec -o <fst-name>.fst <crate-name>
cargo +nightly hacspec -o <ec-name>.ec <crate-name>
```

# Repository Structure

This is a cargo workspace consisting of three main crates:
* [hacspec](language/): the compiler, typechecker and language infrastructure for the hacspec subset of Rust
  * Note that the language infrastructure is excluded from the main workspace of crates, so it won't be build when you launch `cargo build` from the root of the repository.
* [hacspec-lib](lib/): the standard library of hacspec programs
* [hacspec-provider](provider/): a cryptography provider with a set of cryptographic primitives written in hacspec
  * This combines the individual crates from the [examples](examples/) directory and implements the [RustCrypto](https://github.com/RustCrypto/traits) API on top to use them from regular Rust code.

The three main crates make use of a set of additional crates:
* [abstract-integers](utils/abstract-integers/): wrapper around `BigInt` for modular natural integers
* [secret-integers](utils/secret-integers/): wrapper around integer types for constant-timedness
* [unsafe-hacspec-examples](examples-unsafe/): cryptographic specs written in hacspec but not formally typechecked yet(hence the unsafety) as hacspec is a work in progress
* [examples](examples/): cryptographic primitives that have passed the hacspec typechecking
* [hacspec-attributes](utils/attributes): helper for the hacspec library
* [hacspec-dev](utils/dev/): utilities that are not part of the language

Compiled code:
* [fstar](fstar/): contains F* translations of the cryptographic specs, produced by the hacspec compiler
* [easycrypt](easycrypt/): contains EasyCrypt translations of the cryptographic specs, produced by the hacspec compiler

## Contributing

Before starting any work please join the [Zulip chat][chat-link], start a [discussion on Github](https://github.com/hacspec/hacspec/discussions), or file an [issue](https://github.com/hacspec/hacspec/issues) to discuss your contribution.

The main entry points for contributions and some general work items are 
* the [language](language/) if you want to work on the hacspec language itself
  * improve the typechecker
  * improve the existing compiler backends (F* and EasyCrypt)
  * add a new compiler backend
* hacspec [implementations](examples/)
  * implementing new cryptographic primitives in hacspec
  * improve the [provider](provider/)
* the [standard library](lib/)
  * enhance numeric implementations
  * enhance vector arithmetic

# Examples

There's a set of example specs, divided between the [safe](examples/) and [unsafe](examples-unsafe). To run all examples one can use `cargo test`.

## Examples

* [Chacha20](examples/hacspec-chacha20/src/chacha20.rs)
* [Poly1305](examples/hacspec-poly1305/src/poly1305.rs)
* [Chacha20Poly1305](examples/hacspec-chacha20poly1305/src/chacha20poly1305.rs)
* [SHA256](examples/hacspec-sha256/src/sha256.rs)
* [Curve25519](examples/hacspec-curve25519/src/curve25519.rs)
* [NTRU-prime](examples/hacspec-hacspec-ntru-prime/src/ntru-prime.rs)
* [SHA-3](examples/hacspec-sha3/src/sha3.rs)

## Unsafe examples

* [AES 128/256](examples-unsafe/src/aes_gcm/aes.rs)
* [GF 128](examples-unsafe/src/aes_gcm/gf128.rs)
* [AES-GCM 128/256](examples-unsafe/src/aes_gcm/aesgcm.rs)
* [Blake2b](examples-unsafe/src/blake2/blake2b.rs)
* [HKDF-SHA256](examples-unsafe/src/hkdf/hkdf.rs)
* [HMAC-SHA256](examples-unsafe/src/hmac/hmac.rs)
* [P256](examples-unsafe/src/p256/p256.rs)

[//]: # (badges)

[crate-outdated-image]: https://img.shields.io/badge/crate-outdated-red.svg?logo=rust
[crate-hacspec]: https://img.shields.io/crates/v/hacspec.svg?logo=rust
[crate-lib]: https://img.shields.io/crates/v/hacspec-lib.svg?logo=rust
[crate-provider]: https://img.shields.io/crates/v/hacspec-provider.svg?logo=rust
[docs-master-image]: https://img.shields.io/badge/docs-master-blue.svg?logo=rust
[docs-master-link]: https://hacspec.github.io/hacspec/hacspec_lib/index.html
[docs-image]: https://docs.rs/hacspec/badge.svg?logo=rust
[docs-link]: https://docs.rs/hacspec/
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[build-image]: https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg?branch=master&event=push
[build-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Build+%26+Test%22
[deploy-docs-image]: https://github.com/hacspec/hacspec/workflows/Deploy%20Docs/badge.svg?branch=master&event=push
[deploy-docs-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Deploy+Docs%22
[chat-image]: https://img.shields.io/badge/zulip-join_chat-blue.svg?style=social&logo=zulip&color=fedcba
[chat-link]: https://hacspec.zulipchat.com
