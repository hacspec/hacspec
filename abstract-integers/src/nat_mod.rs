
/// Defines a bounded natural integer with modular arithmetic operations
#[macro_export]
macro_rules! define_refined_modular_integer {
    ($name:ident, $base:ident, $max:expr) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
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

        impl $name {
            pub fn max() -> $base {
                $max
            }

            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                $base::from_hex(s).into()
            }

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

        impl From<$base> for $name {
            fn from(x: $base) -> $name {
                $name(x % $max)
            }
        }

        impl Into<$base> for $name {
            fn into(self) -> $base {
                self.0
            }
        }

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
    };
}
