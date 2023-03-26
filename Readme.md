# hacspec [![hacspec chat][chat-image]][chat-link]

<img src="https://raw.githubusercontent.com/hacspec/hacspec/master/img/mascot.png" width=100 style="float: left;"> A specification language for crypto primitives in Rust.

_This is the successor of https://github.com/HACS-workshop/hacspec._

For a quick intro, you can look at the [presentation slides](./presentation_slides.pdf). 
More information is available in the [book](https://hacspec.github.io/book/index.html).
Also, see the Publications below.

## Crates

| Name             | Crates.io                                                                 |                                                                 Docs                                                                  |                        CI                         |
| :--------------- | :------------------------------------------------------------------------ | :-----------------------------------------------------------------------------------------------------------------------------------: | :-----------------------------------------------: |
| hacspec          | [![crates.io][crate-hacspec]](https://crates.io/crates/hacspec)           |                           [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](language/)                           | [![Build & Test Status][build-image]][build-link] |
| hacspec-lib      | [![crates.io][crate-lib]](https://crates.io/crates/hacspec-lib)           |   [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_lib/index.html)    | [![Build & Test Status][build-image]][build-link] |
| hacspec-provider | [![crates.io][crate-provider]](https://crates.io/crates/hacspec-provider) | [![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_provider/index.html) | [![Build & Test Status][build-image]][build-link] |

## Usage

### Writing hacspec

hacspec is always valid Rust code such that starting to write hacspec is as simple as writing Rust code that is compliant with the [language](Language.md) specification.
However, this is very tedious.
It is recommended to use the [hacspec standard library](https://crates.io/crates/hacspec-lib) to write hacspec.
In order to ensure that the code is a hacspec one can use the typecheker.

### Typechecking

Make sure you have at least `rustup 1.23.0`.
The [`rust-toolchain`](./language/rust-toolchain) automatically picks the correct Rust nightly version and components.
The compiler version is currently pinned to `nightly-2023-01-15`.

**Installing the typechecker from the repository**
```
cargo install --path language
```

**Installing the typechecker from crates.io (not always up to date)**
```
cargo install hacspec --version 0.2.0-beta.4
```

**Manually installing dependencies**

First ensure that Rust nightly is installed and the typechecker is installed.

```bash
cd language
rustup toolchain install nightly-2023-01-15
rustup component add --toolchain nightly-2023-01-15 rustc-dev
cargo +nightly-2023-01-15 install hacspec
```

Depending on your system you might also need `llvm-tools-preview`

```bash
rustup component add --toolchain nightly-2023-01-15 llvm-tools-preview
```

**Usage**

In a hacspec crate or workspace directory typechecking can be done as follows now:
(Specifying `+nightly-2023-01-15` is only necessary if it's not specified in the toolchain as it is in this main repository.)

```bash
cargo +nightly-2023-01-15 hacspec <crate-name>
```

Note that the crate dependencies need to be compiled before it can be typechecked.

```bash
cargo +nightly-2023-01-15 build
```

If typechecking succeeds, it should show

```bash
> Successfully typechecked.
```

### Generating code

To generate F\*, EasyCrypt, or Coq code from hacspec the typechecker (see above) is required.

```bash
cargo +nightly-2021-11-14 hacspec -o <fst-name>.fst <crate-name>
cargo +nightly-2021-11-14 hacspec -o <ec-name>.ec <crate-name>
cargo +nightly-2021-11-14 hacspec -o <coq-name>.v <crate-name>
```

## Publications & Other material

* [📕 Tech report](https://hal.inria.fr/hal-03176482)
* [📕 HACSpec: A gateway to high-assurance cryptography](https://github.com/hacspec/hacspec/blob/master/rwc2023-abstract.pdf)
* [📕 Original hacspec paper](https://www.franziskuskiefer.de/publications/hacspec-ssr18-paper.pdf)

### Secondary literature, using hacspec:
* [📕 Last yard](https://eprint.iacr.org/2023/185)

# Repository Structure

This is a cargo workspace consisting of three main crates:

- [hacspec](language/): the compiler, typechecker and language infrastructure for the hacspec subset of Rust
  - Note that the language infrastructure is excluded from the main workspace of crates, so it won't be build when you launch `cargo build` from the root of the repository.
- [hacspec-lib](lib/): the standard library of hacspec programs
- [hacspec-provider](provider/): a cryptography provider with a set of cryptographic primitives written in hacspec
  - This combines the individual crates from the [examples](examples/) directory and implements the [RustCrypto](https://github.com/RustCrypto/traits) API on top to use them from regular Rust code.

The three main crates make use of a set of additional crates:

- [abstract-integers](utils/abstract-integers/): wrapper around `BigInt` for modular natural integers
- [secret-integers](utils/secret-integers/): wrapper around integer types for constant-timedness
- [unsafe-hacspec-examples](examples-unsafe/): cryptographic specs written in hacspec but not formally typechecked yet(hence the unsafety) as hacspec is a work in progress
- [examples](examples/): cryptographic primitives that have passed the hacspec typechecking
- [hacspec-attributes](utils/attributes): helper for the hacspec library
- [hacspec-dev](utils/dev/): utilities that are not part of the language

Compiled code:

- [fstar](fstar/): contains F\* translations of the cryptographic specs, produced by the hacspec compiler
- [easycrypt](easycrypt/): contains EasyCrypt translations of the cryptographic specs, produced by the hacspec compiler
- [coq](coq/): contains Coq translations of the cryptographic specs, produced by the hacspec compiler

## Contributing

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

# Examples

There's a set of example specs, divided between the [safe](examples/) and [unsafe](examples-unsafe). To run all examples one can use `cargo test`.

## Examples

- [Chacha20](examples/chacha20/src/chacha20.rs)
- [Poly1305](examples/poly1305/src/poly1305.rs)
- [Chacha20Poly1305](examples/chacha20poly1305/src/chacha20poly1305.rs)
- [AES 128](examples/aes/src/aes.rs)
- [GF 128](examples/gf128/src/gf128.rs)
- [AES-GCM 128](examples/aes128-gcm/src/aes128-gcm.rs)
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
- [RSA-FDH-VRF](examples/rsa-fdh-vrf/src/rsa-fdh-vrf.rs)
- [ECVRF](examples/rsa-fdh-vrf/src/edwards25519-ecvrf.rs)
- [BIP-340](examples/bip-340/src/bip-340.rs) [text](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki) [blog](https://blog.blockstream.com/half-aggregation-of-bip-340-signatures/), including secp.
- [merlin](examples/merlin)
- [ristretto](examples/ristretto)

## Unsafe examples

- [AES 128/256](examples-unsafe/src/aes_gcm/aes.rs)
- [AES-GCM 128/256](examples-unsafe/src/aes_gcm/aesgcm.rs)
- [Blake2b](examples-unsafe/src/blake2/blake2b.rs)

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
