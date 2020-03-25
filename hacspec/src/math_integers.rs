#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_public_integer!($name, $n);

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
        // unsigned_integer!($base, $bits);
        // secret_modular_integer!($name, $base, $base::from_hex($n));

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
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
            pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> $name {
                $name::from_bytes_le(
                    s.iter()
                        .map(|x| U8::declassify(*x))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )
            }

            pub fn to_byte_seq_le(self) -> Seq<U8> {
                Seq::from(
                    self.to_bytes_le()
                        .iter()
                        .map(|x| U8::classify(*x))
                        .collect::<Vec<U8>>(),
                )
            }

            pub fn from_secret_literal(x: U128) -> $name {
                $name::from_literal(U128::declassify(x))
            }
        }

        impl Numeric for $name {}
        impl NumericBase for $name {
            /// Return largest value that can be represented.
            fn max_val() -> Self {
                unimplemented!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn pow(self, exp: u32) -> Self {
                unimplemented!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self {
                unimplemented!();
            }
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
            /// Division.
            fn div(self, rhs: Self) -> Self {
                unimplemented!();
            }
            /// `self % n`
            fn rem(self, n: Self) -> Self {
                unimplemented!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self {
                unimplemented!();
            }
            /// `|self|`
            fn abs(self) -> Self {
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
            fn greater_than_or_qual_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_bm(self, other: Self) -> Self {
                unimplemented!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self {
                unimplemented!();
            }
        }
    };
}
