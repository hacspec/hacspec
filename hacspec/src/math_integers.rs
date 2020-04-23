#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_public_integer!($name, $n);

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
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
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
macro_rules! signed_public_integer {
    ($name:ident,$n:literal) => {
        abstract_signed_public_integer!($name, $n);

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
                let mut ret = self.modulo(n);
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
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
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
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
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
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
        // TODO: impl Integer for $name
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
                let mut ret = self.modulo(n);
                while ret.less_than(Self::default()) {
                    ret = ret + n;
                }
                ret
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
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
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
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
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
        impl ModNumeric for $name {
            /// (self - rhs) % n.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self + rhs) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self * rhs) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `(self ^ exp) % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn modulo(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `self % n` that always returns a positive integer
            #[cfg_attr(feature="use_attributes", library(hacspec))]
            fn signed_modulo(self, n: Self) -> Self {
                self.modulo(n)
            }
        }
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn max_val() -> Self {
                unimplemented!();
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
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
            /// Division.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            #[cfg_attr(feature="use_attributes", library(library))]
            fn abs(self) -> Self {
                unimplemented!();
            }

            // Comparison functions returning bool.
            #[cfg_attr(feature="use_attributes", library(library))]
            fn equal(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_or_qual(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than(self, other: Self) -> bool {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_or_equal(self, other: Self) -> bool {
                unimplemented!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            #[cfg_attr(feature="use_attributes", library(library))]
            fn not_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            #[cfg_attr(feature="use_attributes", library(library))]
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}
