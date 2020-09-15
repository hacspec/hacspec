//!
//! hacspec consists of three parts:
//! * hacspec library
//! * syntax checker
//! * compiler
//!
//! # The hacspec library
//!
//! The hacspec library implements a comprehensive set of functions to implement
//! succinct cryptographic specs that can be compiled to formal languages such
//! as [F*](https://www.fstar-lang.org/).
//!
//! # The syntax checker
//! TODO:
//! * describe clippy extension
//! * add `cargo hacspec check` command
//!
//! # The compiler
//! TODO:
//! * define compiler interface
//! * add `cargo hacspec fstar` command
//!

mod array;
mod bigint_integers;
mod machine_integers;
mod math_integers;
mod math_util;
pub mod prelude;
mod seq;
mod traits;
mod transmute;
mod util;
mod vec_integers;
mod vec_integers_public;
mod vec_integers_secret;
mod vec_util;

pub use crate::prelude::*;

// XXX: How can we document these things nicely?
// The following are only for documentation purposes.
bytes!(DocSecretBytes, 64);
public_bytes!(DocPublicBytes, 64);
array!(DocSecretArray, 64, U32);
array!(DocPublicArray, 64, u32);
generic_array!(DocParametricArray, 64);
