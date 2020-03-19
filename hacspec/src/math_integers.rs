
#[macro_export]
macro_rules! unsigned_public_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_public_integer!($name, $n);

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max() -> Self {
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
        unimplemented!();
    };
}

#[macro_export]
macro_rules! unsigned_integer {
    ($name:ident,$n:literal) => {
        abstract_unsigned_secret_integer!($name, $n);

        impl Numeric for $name {
            /// Return largest value that can be represented.
            fn max() -> Self {
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
        unimplemented!();
    };
}

#[macro_export]
macro_rules! nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        unsigned_secret_integer!($base, $bits);
        secret_modular_integer!($name, $base, $base::from_hex($n));
    };
}

#[macro_export]
macro_rules! public_nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        unsigned_public_integer!($base, $bits);
        public_modular_integer!($name, $base, $base::from_hex($n));
    };
}
