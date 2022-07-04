
| Name             | Crates.io                                                                 |                                                                 Docs                                                                  |                        CI                         |
| :--------------- | :------------------------------------------------------------------------ | :-----------------------------------------------------------------------------------------------------------------------------------: | :-----------------------------------------------: |
| hacspec          | [![crates.io][crate-hacspec]](https://crates.io/crates/hacspec)           |                           [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](language/)                           | [![Build & Test Status][build-image]][build-link] |
| hacspec-lib      | [![crates.io][crate-lib]](https://crates.io/crates/hacspec-lib)           |   [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_lib/index.html)    | [![Build & Test Status][build-image]][build-link] |
| hacspec-provider | [![crates.io][crate-provider]](https://crates.io/crates/hacspec-provider) | [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_provider/index.html) | [![Build & Test Status][build-image]][build-link] |

# hacspec [![hacspec chat][chat-image]][chat-link]

<img src="https://raw.githubusercontent.com/hacspec/hacspec/master/img/mascot.png" width=100 style="float: left;"> A specification language for crypto primitives in Rust.

_This is the successor of https://github.com/HACS-workshop/hacspec._

# What is hacspec?

Hacspec is a subset of Rust compliant with the [hacspec language specification](Language.md).
As such, every hacspec code is always valid Rust code (and compiles as usual).
However, the opposite is not true.
Some features of Rust are (deliberately) not allowed in hacspec.
Thus, to ensure that written code is valid according to hacspec, we use a custom typechecker packaged as a cargo command, i.e., `cargo hacspec`.
Furthermore, to make writing hacspec easier, there is a [hacspec standard library](https://crates.io/crates/hacspec-lib).

For a quick intro, you can look at the [presentation slides](./presentation_slides.pdf).
An in-depth [technical report](https://hal.inria.fr/hal-03176482) is also available.

# Quickstart

## Install the typechecker

Make sure you have at least `rustup 1.23.0`.
The [`rust-toolchain`](./language/rust-toolchain) config file automatically picks the correct Rust nightly version and components.
The compiler version is currently pinned to `nightly-2021-11-14`.

<details>
  <summary><b>Install from the repository (recommended)</b></summary>

You can install the typechecker from source with ...

```bash
git clone https://github.com/hacspec/hacspec
cd hacspec
cargo install --path language
```
</details>

<details>
  <summary><b>Install from crates.io</b></summary>

Alternatively, you can install cargo-hacspec from crates.io with ...

```bash
cargo install hacspec --version 0.2.0-beta.4
```

Note, however, that it might not be up-to-date.
</details>

<details>
  <summary><b>Install manually</b></summary>

As a third alternative, you can try to install everything manually with ...

```bash
cd language
rustup toolchain install nightly-2021-11-14
rustup component add --toolchain nightly-2021-11-14 rustc-dev
cargo +nightly-2021-11-14 install hacspec
```

Depending on your system, you might also need `llvm-tools-preview`.

```bash
rustup component add --toolchain nightly-2021-11-14 llvm-tools-preview
```
</details>

## Work with the typechecker

### Build dependencies

It is sometimes required to start with a clean build. Thus, we recommend that you execute ...

```shell
cargo clean
```

... first.

Then, build everything with ...

```bash
cargo +nightly-2021-11-14 build
```

**Note**: If you don't want to specify `+nightly-2021-11-14` all the time, copy the [rust-toolchain](rust-toolchain) file into your repository.

### Typecheck your hacspec code

Type checking in a hacspec crate or workspace directory can be done with ...

```bash
cargo +nightly-2021-11-14 hacspec
```

... or ...


```bash
cargo +nightly-2021-11-14 hacspec <crate-name>
```

### Generate verification-friendly code

When the hacspec typechecker returned ...

```bash
> Successfully typechecked.
```

... you are ready to generate some code.

To generate F\*, EasyCrypt, or Coq code from your hacspec, run either of ...

```bash
cargo +nightly-2021-11-14 hacspec -e fst <crate-name> # F*
cargo +nightly-2021-11-14 hacspec -e ec  <crate-name> # EasyCrypt
cargo +nightly-2021-11-14 hacspec -e v   <crate-name> # Coq
```

# Examples

There's a set of example specs, divided between the [safe](examples/) and [unsafe](examples-unsafe).
You can run all examples with `cargo test`.

## Safe examples

- [Chacha20](examples/chacha20/src/chacha20.rs)
- [Poly1305](examples/poly1305/src/poly1305.rs)
- [Chacha20Poly1305](examples/chacha20poly1305/src/chacha20poly1305.rs)
- [SHA256](examples/sha256/src/sha256.rs)
- [SHA512](examples/sha512/src/sha512.rs)
- [Curve25519](examples/curve25519/src/curve25519.rs)
- [NTRU-prime](examples/hacspec-ntru-prime/src/ntru-prime.rs)
- [SHA-3](examples/sha3/src/sha3.rs)
- [HKDF-SHA256](examples/hkdf/src/hkdf.rs)
- [HMAC-SHA256](examples/hmac/src/hmac.rs)
- [BLS12-381](examples/bls12-381/src/bls12-381.rs)
- [BLS12-381 Hash To Curve](examples/bls12-381-hash/src/bls12-381-hash.rs)
- [RIOT bootloade](examples/riot-bootloader/src/lib.rs)
- [GIMLI](examples/gimli/src/gimli.rs)
- [P256](examples/p256/src/p256.rs)
- [ECDSA-P256-SHA256](examples/ecdsa-p256-sha256/src/ecdsa.rs)
- [Ed25519](examples/ed25519/src/ed25519.rs)

## Unsafe examples

- [AES 128/256](examples-unsafe/src/aes_gcm/aes.rs)
- [GF 128](examples-unsafe/src/aes_gcm/gf128.rs)
- [AES-GCM 128/256](examples-unsafe/src/aes_gcm/aesgcm.rs)
- [Blake2b](examples-unsafe/src/blake2/blake2b.rs)

## Repository Structure

This is a cargo workspace consisting of three main crates:

- [hacspec](language/): the compiler, typechecker, and language infrastructure for the hacspec subset of Rust
  - Note that the language infrastructure is excluded from the main workspace of crates, so it won't be build when you launch `cargo build` from the repository's root.
- [hacspec-lib](lib/): the standard library of hacspec programs
- [hacspec-provider](provider/): a cryptography provider with a set of cryptographic primitives written in hacspec
  - This combines the individual crates from the [examples](examples/) directory and implements the [RustCrypto](https://github.com/RustCrypto/traits) API on top to use them from regular Rust code.

The three main crates make use of a set of additional crates:

- [abstract-integers](utils/abstract-integers/): wrapper around `BigInt` for modular natural integers
- [secret-integers](utils/secret-integers/): wrapper around integer types for constant-timedness
- [unsafe-hacspec-examples](examples-unsafe/): cryptographic specs written in hacspec but not formally typechecked yet (hence the unsafety) as hacspec is a work in progress
- [examples](examples/): cryptographic primitives that have passed the hacspec typechecking
- [hacspec-attributes](utils/attributes): helper for the hacspec library
- [hacspec-dev](utils/dev/): utilities that are not part of the language

Compiled code:

- [fstar](fstar/): contains F\* translations of the cryptographic specs, produced by the hacspec compiler
- [easycrypt](easycrypt/): contains EasyCrypt translations of the cryptographic specs, produced by the hacspec compiler
- [coq](coq/): contains Coq translations of the cryptographic specs, produced by the hacspec compiler

# Contributing

Before starting any work please join the [Zulip chat][chat-link], start a [discussion on Github](https://github.com/hacspec/hacspec/discussions), or file an [issue](https://github.com/hacspec/hacspec/issues) to discuss your contribution.

The main entry points for contributions and some general work items are

- the [language](language/) if you want to work on the hacspec language itself
  - improve the typechecker
  - improve the existing compiler backends (F\* and EasyCrypt)
  - add a new compiler backend
- hacspec [implementations](examples/)
  - implementing new cryptographic primitives in hacspec
  - improve the [provider](provider/)
- the [standard library](lib/)
  - enhance numeric implementations
  - enhance vector arithmetic

# Publications & Other material

* [📕 Tech report](https://hal.inria.fr/hal-03176482)
* [📕 Original hacspec paper](https://www.franziskuskiefer.de/publications/hacspec-ssr18-paper.pdf)

[//]: # "badges"
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
