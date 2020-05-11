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

pub mod array;
pub mod bigint_integers;
pub mod machine_integers;
pub mod math_integers;
pub mod math_util;
pub mod traits;
pub mod prelude;
pub mod seq;
pub mod util;
pub mod vec_integers;
pub mod vec_integers_secret;
pub mod vec_integers_public;
pub mod vec_util;
pub mod transmute;

use crate::prelude::*;

// XXX: How can we document these things nicely?
// The following are only for documentation purposes.
bytes!(DocSecretBytes, 64);
public_bytes!(DocPublicBytes, 64);
array!(DocSecretArray, 64, U32);
array!(DocPublicArray, 64, u32);
generic_array!(DocParametricArray, 64);

bytes!(U16Word, 2);
bytes!(U32Word, 4);
bytes!(U64Word, 8);
bytes!(U128Word, 16);

public_bytes!(u16Word, 2);
public_bytes!(u32Word, 4);
public_bytes!(u64Word, 8);
public_bytes!(u128Word, 16);
