# hacspec provider

[![crates.io][crate-provider]](https://crates.io/crates/hacspec-provider) 
[![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_provider/index.html)
[![Build & Test Status][build-image]][build-link]

The hacspec provider is a cryptography provider with a set of cryptographic primitives written in hacspec.
It combines the individual crates from the [examples](../examples/) directory and implements the [RustCrypto](https://github.com/RustCrypto/traits) API on top to use them from regular Rust code.

[//]: # (badges)

[crate-provider]: https://img.shields.io/crates/v/hacspec-provider.svg?logo=rust
[build-image]: https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg?branch=master&event=push
[build-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Build+%26+Test%22
