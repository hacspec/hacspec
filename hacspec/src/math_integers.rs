

use crate::prelude::*;
use crate::numeric::Numeric;

#[macro_export]
macro_rules! nat_mod {
    ($name:ident,$n:expr) => {
        
    };
}

// TODO: move to abstract integers
#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        define_abstract_integer_checked!($name, $n);
    };
}

#[macro_export]
macro_rules! signed_public_integer {
    ($name:ident,$n:literal) => {
        
    };
}

#[macro_export]
macro_rules! unsigned_secret_integer {
    ($name:ident,$n:literal) => {
        
    };
}

#[macro_export]
macro_rules! signed_secret_integer {
    ($name:ident,$n:literal) => {
        
    };
}

// // 256-bit unsigned public integer
// unsigned_public_integer!(PUint256, 256);
// // 256-bit signed public integer
// signed_public_integer!(PInt256, 256);
// // 256-bit unsigned secret integer
// unsigned_secret_integer!(Uint256, 256);
// // 256-bit signed secret integer
// signed_secret_integer!(Int256, 256);
