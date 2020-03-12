# Rust secret integers

This simple crate provides integer wrappers that guarantee that they are being used in a constant-time fashion. Hence, division and direct comparison are disallowed. Using Rust's type system, this crate will help the compiler check systematically whether your cryptographic code is constant-time relative to secret inputs.

To use the crate, just import everything (`use secret_integers::*;`) and replace your integer types with uppercase versions of their names (e.g. `u8` -> `U8`).

## Examples

Two examples show how to use the crate : [Dalek](https://github.com/denismerigoux/rust-secret-integers/tree/master/examples/dalek.rs)
and [Chacha20](https://github.com/denismerigoux/rust-secret-integers/tree/master/examples/chacha20.rs).
To build theses examples, use

    cargo build --example dalek
    cargo build --example chacha20

However, if you try:

    cargo build --example biguint

You will get the following error message:

```
error[E0599]: no method named `leading_zeros` found for type `&secret_integers::U32` in the current scope
--> examples/biguint.rs:24:46
 |
24 |        let zeros = self.data.last().unwrap().leading_zeros();
 |                                              ^^^^^^^^^^^^^

error[E0369]: binary operation `!=` cannot be applied to type `secret_integers::U32`
--> examples/biguint.rs:48:11
 |
48 |     while r != 0 {
 |           ^^^^^^
 |
 = note: an implementation of `std::cmp::PartialEq` might be missing for `secret_integers::U32`
```
