use crate::prelude::*;

impl Integer for BigInt {
    /// `NUM_BITS` is arbitrary for `BigInt`, so this i `0`.
    const NUM_BITS: usize = 0;

    #[inline]
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn ZERO() -> Self {
        BigInt::from(0)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn ONE() -> Self {
        BigInt::from(1)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn TWO() -> Self {
        BigInt::from(2)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn from_literal(val: u128) -> Self {
        BigInt::from(val)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn from_hex_string(s: &String) -> Self {
        BigInt::from_str(s).unwrap()
    }
}
impl Numeric for BigInt {
    /// Return largest value that can be represented.
    fn max_val() -> Self {
        unimplemented!();
    }

    fn wrap_add(self, rhs: Self) -> Self {
        self + rhs
    }
    fn wrap_sub(self, rhs: Self) -> Self {
        self - rhs
    }
    fn wrap_mul(self, rhs: Self) -> Self {
        self * rhs
    }
    fn wrap_div(self, rhs: Self) -> Self {
        unimplemented!();
    }

    /// `self ^ exp` where `exp` is a `u32`.
    fn exp(self, exp: u32) -> Self {
        unimplemented!();
    }
    /// `self ^ exp` where `exp` is a `Self`.
    fn pow_self(self, exp: Self) -> Self {
        unimplemented!();
    }
    /// Division.
    fn divide(self, rhs: Self) -> Self {
        unimplemented!();
    }
    /// Invert self modulo n.
    fn inv(self, n: Self) -> Self {
        unimplemented!();
    }

    // Comparison functions returning bool.
    fn equal(self, other: Self) -> bool {
        unimplemented!();
    }
    fn greater_than(self, other: Self) -> bool {
        unimplemented!();
    }
    fn greater_than_or_qual(self, other: Self) -> bool {
        unimplemented!();
    }
    fn less_than(self, other: Self) -> bool {
        unimplemented!();
    }
    fn less_than_or_equal(self, other: Self) -> bool {
        unimplemented!();
    }

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    fn not_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn greater_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn greater_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn less_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    fn less_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
}

impl ModNumeric for BigInt {
    /// (self - rhs) % n.
    #[cfg_attr(feature="use_attributes", library(library))]
    fn sub_mod(self, rhs: Self, n: Self) -> Self {
        (self - rhs) % n
    }
    /// `(self + rhs) % n`
    #[cfg_attr(feature="use_attributes", library(library))]
    fn add_mod(self, rhs: Self, n: Self) -> Self {
        (self + rhs) % n
    }
    /// `(self * rhs) % n`
    #[cfg_attr(feature="use_attributes", library(library))]
    fn mul_mod(self, rhs: Self, n: Self) -> Self {
        (self * rhs) % n
    }
    /// `(self ^ exp) % n`
    #[cfg_attr(feature="use_attributes", library(library))]
    fn pow_mod(self, exp: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `self % n`
    #[cfg_attr(feature="use_attributes", library(library))]
    fn modulo(self, n: Self) -> Self {
        self % n
    }
    /// `self % n` that always returns a positive integer
    #[cfg_attr(feature="use_attributes", library(hacspec))]
    fn signed_modulo(self, n: Self) -> Self {
        unimplemented!();
    }
    /// `|self|`
    #[cfg_attr(feature = "use_attributes", library(hacspec))]
    fn absolute(self) -> Self {
        self.abs()
    }
}
