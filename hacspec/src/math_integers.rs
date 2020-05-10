// TODO: Can we implement Integer for math integers? Do we need to?

#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_public_integer!($name, $n);

        impl Numeric for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs) % n
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs) % n
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs) % n
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp, n)
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                $name::max_value()
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into(), Self::max_val())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp.into(), Self::max_val())
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                $name::inv(self, n)
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                self == other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                self >= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                if !self.equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                if self.equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                if self.greater_than(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self.greater_than_or_qual(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                if self.less_than(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self.less_than_or_equal(other) {
                    Self::max_val()
                } else {
                    Self::from_literal(0)
                }
            }
        }
    };
}

#[macro_export]
macro_rules! signed_public_integer {
    ($name:ident,$n:literal) => {
        abstract_signed_public_integer!($name, $n);

        impl Numeric for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).signed_modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).signed_modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).signed_modulo(n)
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp, n).signed_modulo(n)
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: implement in abstract-integers
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                unimplemented!();
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                Self::max_value()
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into(), Self::max_val())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp, Self::max_val())
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                $name::inv(self, n)
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                self == other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                self <= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                if !self.equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                if self.equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                if self.greater_than(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self.greater_than_or_qual(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                if self.less_than(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self.less_than_or_equal(other) {
                    Self::from_signed_literal(-1)
                } else {
                    Self::from_signed_literal(0)
                }
            }
        }
    };
}

#[macro_export]
macro_rules! unsigned_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_secret_integer!($name, $n);

        impl Numeric for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! signed_integer {
    ($name:ident,$n:literal) => {
        abstract_signed_secret_integer!($name, $n);

        impl Numeric for $name {}
        impl Integer for $name {
            const NUM_BITS: u32 = $n;

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            /// Read hex string to `Self`.
            fn from_hex_string(s: &String) -> Self {
                let sign_str = if s.starts_with("-") {
                    "-"
                } else {
                    "+"
                };
                Self::from_hex(&sign_str, &s.replace("0x", "").replace("-", "").replace("+", ""))
            }
        }
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                (self - rhs).modulo(n)
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                (self + rhs).modulo(n)
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                (self * rhs).modulo(n)
            }
            /// `(self ^ exp) % n`
            /// TODO: implement
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n` that always returns a positive integer
            /// FIXME: implement ct
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                let mut ret = self.modulo(n);
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
            }
            /// `|self|`
            /// TODO: implement in abstract-integers
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                unimplemented!();
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        abstract_nat_mod!($name, $base, $bits, $n);

        impl Numeric for $name {}
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            /// TODO: implement in abstract-integers
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                unimplemented!();
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn max_val() -> Self {
                unimplemented!();
            }

            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn wrap_div(self, rhs: Self) -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn exp(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn divide(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! public_nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        unsigned_public_integer!($base, $bits);
        abstract_public_modular_integer!($name, $base, $base::from_hex($n));

        // FIXME: check if we really need this and maybe move this somewhere.
        impl $name {
            #[cfg_attr(feature="use_attributes", library(to_remove))]
            pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> $name {
                $name::from_le_bytes(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
            }

            #[cfg_attr(feature="use_attributes", library(to_remove))]
            pub fn to_public_byte_seq_le(self) -> Seq<u8> {
                Seq::from_vec(
                    self.to_le_bytes()
                )
            }

            #[cfg_attr(feature="use_attributes", library(to_remove))]
            pub fn to_byte_seq_le(self) -> Seq<U8> {
                Seq::from_vec(
                    self.to_le_bytes()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }

            #[cfg_attr(feature="use_attributes", library(to_remove))]
            pub fn from_secret_literal(x: U128) -> $name {
                $name::from_literal(U128::declassify(x))
            }
        }

        impl Numeric for $name {}
        impl Integer for $name {
            const NUM_BITS: u32 = $bits;

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ZERO() -> Self {
                Self::from_literal(0)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn ONE() -> Self {
                Self::from_literal(1)
            }
            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn TWO() -> Self {
                Self::from_literal(2)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_literal(val: u128) -> Self {
                Self::from_literal(val)
            }

            #[inline]
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn from_hex_string(s: &String) -> Self {
                Self::from_hex(&s.replace("0x", ""))
            }
        }
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                self - rhs
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                self + rhs
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                self * rhs
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                self.pow_felem(exp)
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn modulo(self, n: Self) -> Self {
                self % n
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
            /// `|self|`
            #[cfg_attr(feature = "use_attributes", library(hacspec))]
            fn absolute(self) -> Self {
                self
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn max_val() -> Self {
                (Self::max() - $base::from_literal(1)).into()
            }

            #[cfg_attr(feature="use_attributes", library(library))]
            fn wrap_add(self, rhs: Self) -> Self {
                self + rhs
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn wrap_sub(self, rhs: Self) -> Self {
                self - rhs
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn wrap_mul(self, rhs: Self) -> Self {
                self * rhs
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn wrap_div(self, rhs: Self) -> Self {
                self / rhs
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn exp(self, exp: u32) -> Self {
                self.pow(exp.into())
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn pow_self(self, exp: Self) -> Self {
                self.pow_felem(exp)
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn divide(self, rhs: Self) -> Self {
                self / rhs
            }
            /// Invert self modulo n.
            /// **NOTE:** `n` is ignored and inversion is done with respect to
            ///            the modulus.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn inv(self, n: Self) -> Self {
                self.inv()
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn equal(self, other: Self) -> bool {
                self == other
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than(self, other: Self) -> bool {
                self > other
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                self >= other
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than(self, other: Self) -> bool {
                self < other
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_or_equal(self, other: Self) -> bool {
                self <= other
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            // Return $bits-1 1s as we can't represent 0xF..F.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn not_equal_bm(self, other: Self) -> Self {
                if self != other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn equal_bm(self, other: Self) -> Self {
                if self == other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_bm(self, other: Self) -> Self {
                if self > other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                if self >= other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_bm(self, other: Self) -> Self {
                if self < other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                if self <= other {
                    (Self::ONE() << ($bits-1))-Self::ONE()
                } else {
                    Self::ZERO()
                }
            }
        }
    };
}
