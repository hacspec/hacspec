//! # Hacspec Provider
//!
//! This crate provides a high-level API for hacspec implementations in
//! [examples](https://github.com/hacspec/hacspec/tree/master/examples).
//! The provider implements the [RustCrypto traits](https://github.com/RustCrypto/traits)
//! API to be interoperable with other implementations.
//!
//! This crate does not have tests on its own but is tested through the
//! [utils test](https://github.com/hacspec/hacspec/tree/master/utils/rc-tests).

mod provider;
pub use provider::{
    aead, Aead, AeadCore, AeadInPlace, Chacha20Poly1305, Error, Key, NewAead, Nonce, Payload, Tag,
};
