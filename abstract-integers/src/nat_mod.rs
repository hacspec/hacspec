#[macro_export]
macro_rules! modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        #[derive(Clone, Copy, Default)]
        pub struct $name($base);

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: $base = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: $base = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl From<$base> for $name {
            fn from(x: $base) -> $name {
                $name(x.rem($max))
            }
        }

        impl Into<$base> for $name {
            fn into(self) -> $base {
                self.0
            }
        }

        impl $name {
            pub fn max() -> $base {
                $max
            }

            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                $base::from_hex(s).into()
            }

            #[allow(dead_code)]
            pub fn from_bytes_le(v: &[u8]) -> Self {
                $base::from_bytes_le(v).into()
            }

            #[allow(dead_code)]
            pub fn to_bytes_le(self) -> Vec<u8> {
                $base::to_bytes_le(self.into())
            }

            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            pub fn bit(self, i: usize) -> bool {
                $base::bit(self.into(), i)
            }

            #[allow(dead_code)]
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigUint::from(x);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                $name(big_x.into())
            }

            #[allow(dead_code)]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigUint::from(x as u128);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                $name(big_x.into())
            }
        }
    };
}

// FIXME: Implement ct algorithms
#[macro_export]
macro_rules! abstract_secret_modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        modular_integer!($name, $base, $max);

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a + b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let max: BigUint = $max.into();
                let c: BigUint = if b > a { max.clone() - b + a } else { a - b };
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a * b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }
    };
}

#[macro_export]
macro_rules! abstract_public_modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        modular_integer!($name, $base, $max);

        // TODO: implement PartialEq, Eq, PartialOrd, Ord,
        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0)
            }
        }
        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
        impl Eq for $name {}

        /// **Warning**: wraps on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a + b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let max: BigUint = $max.into();
                let c: BigUint = if b > a { max.clone() - b + a } else { a - b };
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: wraps on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a * b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a / b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                let a: $base = self.into();
                let b: $base = rhs.into();
                let a: BigUint = a.into();
                let b: BigUint = b.into();
                let c: BigUint = a % b;
                let max: BigUint = $max.into();
                let d: BigUint = c % max;
                let d: $base = d.into();
                d.into()
            }
        }

        impl Not for $name {
            type Output = $name;
            fn not(self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitOr for $name {
            type Output = $name;
            fn bitor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shr<u32> for $name {
            type Output = $name;
            fn shr(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl Shl<u32> for $name {
            type Output = $name;
            fn shl(self, rhs: u32) -> Self::Output {
                unimplemented!();
            }
        }

        impl $name {
            #[allow(dead_code)]
            pub fn inv(self) -> Self {
                let base: $base = self.into();
                base.inv(Self::max()).into()
            }

            #[allow(dead_code)]
            pub fn pow_felem(self, exp: Self) -> Self {
                let base: $base = self.into();
                base.pow_felem(exp.into(), Self::max()).into()
            }
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u128) -> Self {
                let base: $base = self.into();
                base.pow(exp, Self::max()).into()
            }
        }
    };
}

#[macro_export]
macro_rules! abstract_nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        abstract_unsigned_secret_integer!($base, $bits);
        abstract_secret_modular_integer!($name, $base, $base::from_hex($n));
    };
}

#[macro_export]
macro_rules! abstract_public_nat_mod {
    ($name:ident,$base:ident,$bits:literal,$n:literal) => {
        abstract_unsigned_public_integer!($base, $bits);
        abstract_public_modular_integer!($name, $base, $base::from_hex($n));
    };
}

// ============ Legacy API ============

/// Defines a bounded natural integer with modular arithmetic operations
#[macro_export]
macro_rules! define_refined_modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        abstract_public_modular_integer!($name, $base, $max);
    };
}
