#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

use hacspec_lib::*;

#[cfg(not(feature = "hacspec"))]
use creusot_contracts::{ensures, requires};

#[requires(x == y)]
#[ensures(result == true)]
pub fn ensure_something (x : u8, y : u8) -> bool {
    x == y
}

