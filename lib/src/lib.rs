//! # The hacspec standard library
//!
//! ## Data types
//! The standard library provides two main data types.
//!
//! ### Sequences
//! Sequences [`Seq`](`seq::Seq`) arrays with a fixed length set at runtime.
//! They replace Rust vectors, which are not allowed in hacspec.
//!
//! See the [seq](`mod@seq`) module documentation for more details.
//!
//! ```
//! use hacspec_lib::prelude::*;
//! let x = Seq::<U128>::from_public_slice(&[5, 2, 7, 8, 9]);
//! let x = Seq::<u128>::from_native_slice(&[5, 2, 7, 8, 9]);
//! let y = ByteSeq::from_hex("0388dace60b6a392f328c2b971b2fe78");
//! ```
//!
//! ### Arrays
//! Arrays have a fixed length that is known at compile time.
//! They replace the Rust arrays, which are not allowed in hacspec.
//!
//! See the [arrays](`mod@array`) module documentation for more details.
//!
//! To define a new array type with name `State`, holding `16` `u32` run
//!
//! ```
//! use hacspec_lib::prelude::*;
//! array!(State, 16, u32, type_for_indexes: StateIdx);
//! ```
//!
//! The `type_for_indexes` defines the index type for this array as `StateIdx`.
//! Such an array can now be used similarly to regular Rust arrays.
//!
//! ```
//! use hacspec_lib::prelude::*;
//! array!(State, 16, u32, type_for_indexes: StateIdx);
//! fn modify_state(mut state: State) -> State {
//!     state[1] = state[1] + state[2];
//!     state
//! }
//! ```
//!
//! ## Numeric Types
//! The standard library provides two main numeric types.
//!
//! ### Math Integers
//! Integers with a fixed upper bound on the byte length.
//! See the [math integer](`mod@math_integers`) module documentation for more details.
//!
//! The following example defines and uses the type `LargeSecretInteger` that can hold unsigned integers up to 2^233-1.
//!
//! ```
//! use hacspec_lib::prelude::*;
//! unsigned_integer!(LargeSecretInteger, 233);
//! let a = LargeSecretInteger::from_literal(1);
//! let b = LargeSecretInteger::from_literal(2);
//! let c = a + b;
//! let result = std::panic::catch_unwind(|| {
//!     // This panics because comparing secret math integers is currently not support.
//!     assert!(c.equal(LargeSecretInteger::from_literal(3)));
//! });
//! assert!(result.is_err());
//! let _max = LargeSecretInteger::from_hex("1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
//! ```
//!
//! ## Secret Integers
//! All numeric types can be public or secret.
//! By default they are secret types.
//! Public types are prefixed with `public_`.
//!
//! ### Secret Machine Integers
//! The regular machine integers Rust provides are considered public integers.
//! This standard library defines secret variants for all public machine integers defined as follows.
//!
//! Unsigned secret integers: `U8, U16, U32, U64, U128`
//!
//! Signed secret integers: `I8, I16, I32, I64, I128`
//!
//! See the [secret integers](`secret_integers`) for details.

pub mod array;
mod bigint_integers;
mod machine_integers;
pub mod math_integers;
mod math_util;
pub mod prelude;
pub mod seq;
mod traits;
mod transmute;
mod util;
mod vec_integers;
mod vec_integers_public;
mod vec_integers_secret;
mod vec_util;

pub use crate::prelude::*;
