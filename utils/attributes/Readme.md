# hacspec attributes

[![crates.io][crate-attributes]](https://crates.io/crates/hacspec-attributes) 
[![Docs](https://img.shields.io/badge/docs-master-blue.svg?logo=rust)](https://hacspec.github.io/hacspec/hacspec_attributes/index.html)
[![Build & Test Status][build-image]][build-link]

This crate holds implements hacspec attributes used only in the [hacspec library](../../lib/) as well as attributes that can be used in hacspecs.

## Features
### hacspec_unsafe
This is a **default feature** that enables the `#[hacspec_unsafe]` attribute.
The `#[hacspec_unsafe]` attribute can be used to call Rust code from hacspec.
A function with the `#[hacspec_unsafe]` attribute must have a signature within hacspec but can use Rust in its body.
A function with `#[hacspec_unsafe(outside)]` is completely ignored by the hacspec typechecker.

### print_attributes
This feature is used within the hacspec library to mark functions according to their language affiliation.

### update_allowlist
This feature is used within the hacspec library.

[//]: # (badges)

[crate-attributes]: https://img.shields.io/crates/v/hacspec-attributes.svg?logo=rust
[build-image]: https://github.com/hacspec/hacspec/workflows/Build%20&%20Test/badge.svg?branch=master&event=push
[build-link]: https://github.com/hacspec/hacspec/actions?query=workflow%3A%22Build+%26+Test%22
