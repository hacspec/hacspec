# hacspec library


[![crates.io][crate-lib]](https://crates.io/crates/hacspec-lib) 
[![Docs][docs-image]](https://hacspec.github.io/hacspec/hacspec_lib/index.html)
[![Build & Test Status][build-image]][build-link]

This is the hacspec standard library for hacspec programs.

### Print attributes and statistics

Using the `attributes` crate, we can monitor the number of functions in each
category : primitive, external, library, to remove, internal.

To get the statistics simply use

    bash get_func_stats.sh

*Note* : you need to have the nightly Rust toolchain installed to enable
this feature. Install it using :

    rustup toolchain install nightly

[//]: # (badges)

[crate-lib]: https://img.shields.io/crates/v/hacspec-lib.svg?logo=rust
[docs-image]: https://img.shields.io/badge/docs-master-blue.svg?logo=rust
[build-image]: https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg?branch=master&event=push
[build-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Build+%26+Test%22
