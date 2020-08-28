#![allow(unused_variables)]
///!
///! Implement vector arithmetic for array.
///!
use crate::prelude::*;

#[macro_export]
macro_rules! _implement_array_arithmetic_base {
    ($name:ident) => {
        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn add(self, rhs: $name) -> $name {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].wrapping_add(rhs[i])
                }
                out
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn sub(self, rhs: $name) -> $name {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = self[i].wrapping_sub(rhs[i])
                }
                out
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn mul(self, rhs: $name) -> $name {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = self[i].wrap_mul(rhs[i]);
                }
                out
            }
        }

        /// Bit-wise not operation on the coefficients.
        impl Not for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn not(self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = !self[i]
                }
                out
            }
        }

        /// Bit-wise or operation on the coefficients.
        impl BitOr for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = self[i] | rhs[i]
                }
                out
            }
        }

        /// Bit-wise xor operation on the coefficients.
        impl BitXor for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = self[i] ^ rhs[i]
                }
                out
            }
        }

        /// Bit-wise and operation on the coefficients.
        impl BitAnd for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn bitand(self, rhs: Self) -> Self::Output {
                let mut out = Self::new();
                for i in 0..Self::length() {
                    out[i] = self[i] & rhs[i]
                }
                out
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_unsigned_public {
    ($name:ident) => {
        _implement_array_arithmetic_base!($name);

        impl PartialOrd for $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl Eq for $name {}

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            fn div(self, rhs: $name) -> $name {
                let mut out = Self::new();
                for i in 0..self.len() {
                    out[i] = self[i].wrapping_div(rhs[i])
                }
                out
            }
        }
    };
}

#[macro_export]
macro_rules! _implement_numeric_unsigned_secret {
    ($name:ident) => {
        _implement_array_arithmetic_base!($name);
    };
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_mul<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].mul_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_mul(y[i]);
        }
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_add<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].add_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_add(y[i]);
        }
    }
    out
}

#[inline]
#[cfg_attr(feature = "use_attributes", in_hacspec)]
pub fn vec_poly_sub<T: Numeric + Copy, U: SeqTrait<T>>(x: U, y: U, n: T) -> U {
    debug_assert!(x.len() == y.len());
    let mut out = U::create(x.len());
    for i in 0..x.len() {
        if !n.equal(T::default()) {
            out[i] = x[i].sub_mod(y[i], n);
        } else {
            out[i] = x[i].wrap_sub(y[i]);
        }
    }
    out
}
