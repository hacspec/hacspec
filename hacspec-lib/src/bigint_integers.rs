#![allow(unused_variables)]
use crate::prelude::*;

impl Integer for BigInt {
    /// `NUM_BITS` is arbitrary for `BigInt`, so this i `0`.
    const NUM_BITS: usize = 0;

    #[inline]
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn ZERO() -> Self {
        BigInt::from(0)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn ONE() -> Self {
        BigInt::from(1)
    }
    #[inline]
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn TWO() -> Self {
        BigInt::from(2)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn from_literal(val: u128) -> Self {
        BigInt::from(val)
    }

    #[inline]
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn from_hex_string(s: &String) -> Self {
        BigInt::from_str(s).unwrap()
    }
}
impl Numeric for BigInt {
    /// Return largest value that can be represented.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn max_val() -> Self {
        unimplemented!();
    }

    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn wrap_add(self, rhs: Self) -> Self {
        self + rhs
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn wrap_sub(self, rhs: Self) -> Self {
        self - rhs
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn wrap_mul(self, rhs: Self) -> Self {
        self * rhs
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn wrap_div(self, rhs: Self) -> Self {
        unimplemented!();
    }

    /// `self ^ exp` where `exp` is a `u32`.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn exp(self, exp: u32) -> Self {
        unimplemented!();
    }
    /// `self ^ exp` where `exp` is a `Self`.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn pow_self(self, exp: Self) -> Self {
        unimplemented!();
    }
    /// Division.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn divide(self, rhs: Self) -> Self {
        unimplemented!();
    }
    /// Invert self modulo n.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn inv(self, n: Self) -> Self {
        unimplemented!();
    }

    // Comparison functions returning bool.
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn equal(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn greater_than(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn greater_than_or_qual(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn less_than(self, other: Self) -> bool {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn less_than_or_equal(self, other: Self) -> bool {
        unimplemented!();
    }

    // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn not_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn greater_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn greater_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn less_than_bm(self, other: Self) -> Self {
        unimplemented!();
    }
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn less_than_or_equal_bm(self, other: Self) -> Self {
        unimplemented!();
    }
}

impl ModNumeric for BigInt {
    /// (self - rhs) % n.
    #[cfg_attr(feature="use_attributes", external(external))]
    fn sub_mod(self, rhs: Self, n: Self) -> Self {
        (self - rhs) % n
    }
    /// `(self + rhs) % n`
    #[cfg_attr(feature="use_attributes", external(external))]
    fn add_mod(self, rhs: Self, n: Self) -> Self {
        (self + rhs) % n
    }
    /// `(self * rhs) % n`
    #[cfg_attr(feature="use_attributes", external(external))]
    fn mul_mod(self, rhs: Self, n: Self) -> Self {
        (self * rhs) % n
    }
    /// `(self ^ exp) % n`
    #[cfg_attr(feature="use_attributes", external(external))]
    fn pow_mod(self, exp: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `self % n`
    #[cfg_attr(feature="use_attributes", external(external))]
    fn modulo(self, n: Self) -> Self {
        self % n
    }
    /// `self % n` that always returns a positive integer
    #[cfg_attr(feature="use_attributes", external(hacspec))]
    fn signed_modulo(self, n: Self) -> Self {
        unimplemented!();
    }
    /// `|self|`
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn absolute(self) -> Self {
        self.abs()
    }
}

impl PublicInteger for BigInt {
    type SecretVersion = BigInt;
}

impl SecretInteger for BigInt {
    type PublicVersion = BigInt;
    #[cfg_attr(feature = "use_attributes", external(hacspec))]
    fn classify(x: Self::PublicVersion) -> Self {
        x
    }
}
