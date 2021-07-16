#![allow(unused_variables)]
use crate::prelude::*;

// TODO: this won't allow us to split between signed and unsigned.
impl<T: Numeric + SecretInteger + Copy> ModNumeric for Seq<T> {
    /// (self - rhs) % n.
    fn sub_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self + rhs) % n`
    fn add_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self * rhs) % n`
    fn mul_mod(self, rhs: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `(self ^ exp) % n`
    fn pow_mod(self, exp: Self, n: Self) -> Self {
        unimplemented!();
    }
    /// `self % n`
    fn modulo(self, n: Self) -> Self {
        unimplemented!();
    }
    fn signed_modulo(self, _n: Self) -> Self {
        unimplemented!();
    }
    /// `|self|` (coefficient-wise)
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn absolute(self) -> Self {
        unimplemented!();
    }
}
impl<T: Numeric + SecretInteger + Copy> Numeric for Seq<T> {
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

/// Polynomial multiplication on ℤ\[x\]
impl<T: Numeric + SecretInteger + Copy> Mul for Seq<T> {
    type Output = Self;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn mul(self, rhs: Self) -> Self::Output {
        vec_poly_mul(self, rhs, T::default())
    }
}

/// Polynomial subtraction on ℤ\[x\]
impl<T: Numeric + SecretInteger + Copy> Sub for Seq<T> {
    type Output = Self;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn sub(self, rhs: Self) -> Self::Output {
        vec_poly_sub(self, rhs, T::default())
    }
}

/// Polynomial addition on ℤ\[x\]
impl<T: Numeric + SecretInteger + Copy> Add for Seq<T> {
    type Output = Self;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn add(self, rhs: Self) -> Self::Output {
        vec_poly_add(self, rhs, T::default())
    }
}

impl<T: Numeric + SecretInteger + Copy> Not for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn not(self) -> Self::Output {
        let mut out = Self::new(self.len());
        for (a, b) in out.b.iter_mut().zip(self.b.iter()) {
            *a = !*b;
        }
        out
    }
}

impl<T: Numeric + SecretInteger + Copy> BitOr for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn bitor(self, rhs: Self) -> Self::Output {
        let mut out = Self::new(self.len());
        for (a, (b, c)) in out.b.iter_mut().zip(self.b.iter().zip(rhs.b.iter())) {
            *a = *b | *c;
        }
        out
    }
}

impl<T: Numeric + SecretInteger + Copy> BitXor for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut out = Self::new(self.len());
        for (a, (b, c)) in out.b.iter_mut().zip(self.b.iter().zip(rhs.b.iter())) {
            *a = *b ^ *c;
        }
        out
    }
}

impl<T: Numeric + SecretInteger + Copy> BitAnd for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn bitand(self, rhs: Self) -> Self::Output {
        let mut out = Self::new(self.len());
        for (a, (b, c)) in out.b.iter_mut().zip(self.b.iter().zip(rhs.b.iter())) {
            *a = *b & *c;
        }
        out
    }
}

impl<T: Numeric + SecretInteger + Copy> Shr<usize> for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn shr(self, rhs: usize) -> Self::Output {
        unimplemented!();
    }
}

impl<T: Numeric + SecretInteger + Copy> Shl<usize> for Seq<T> {
    type Output = Seq<T>;
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    fn shl(self, rhs: usize) -> Self::Output {
        unimplemented!();
    }
}
