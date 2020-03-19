#![allow(unused_macros)]

#[macro_export]
macro_rules! abstract_int {
    ($name:ident, $bits:literal) => {
        #[derive(Clone, Copy)]
        pub struct $name {
            b: [u8; ($bits + 7) / 8],
            sign: Sign,
        }

        impl Default for $name {
            fn default() -> $name {
                $name {
                    b: [0u8; ($bits + 7) / 8],
                    sign: Sign::Plus,
                }
            }
        }

        // impl Into<BigInt> for $name {
        //     fn into(self) -> BigInt {
        //         BigInt::from_bytes_be(self.sign, &self.b)
        //     }
        // }
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigUint = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigUint = (*self).into();
                write!(f, "{}", uint)
            }
        }
    }
}

#[macro_export]
macro_rules! abstract_unsigned {
    ($name:ident, $bits:literal) => {
        abstract_int!($name, $bits);

        impl From<BigUint> for $name {
            fn from(x: BigUint) -> $name {
                let max_value = BigUint::from(1u32) <<  $bits;
                assert!(x < max_value, "BigUint {} is too big x for type {}!", x, stringify!($name));
                let repr = x.to_bytes_be();
                if repr.len() > ($bits + 7) / 8 {
                    panic!("BigUint {} too big for type {}", x, stringify!($name))
                }
                let mut out = [0u8; ($bits + 7) / 8];
                let upper = out.len();
                let lower = upper - repr.len();
                out[lower..upper].copy_from_slice(&repr);
                $name {
                    b: out,
                    sign: Sign::Plus,
                }
            }
        }
        impl Into<BigUint> for $name {
            fn into(self) -> BigUint {
                BigUint::from_bytes_be(&self.b)
            }
        }
    };
}

/// Defines a bounded natural integer with regular arithmetic operations, checked for overflow
/// and underflow.
#[macro_export]
macro_rules! define_abstract_integer_checked {
    ($name:ident, $bits:literal) => {
        abstract_unsigned!($name, $bits);

        impl $name {
            fn max() -> BigUint {
                BigUint::from(2u32).shl($bits)
            }

            fn hex_string_to_bytes(s: &str) -> Vec<u8> {
                assert!(s.len() % 2 == 0, "length of hex string {}: {}",s, s.len());
                let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
                    .collect();
                b.expect("Error parsing hex string")
            }

            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                BigUint::from_bytes_be(&Self::hex_string_to_bytes(s)).into()
            }

            #[allow(dead_code)]
            pub fn from_bytes_le(v: &[u8]) -> Self {
                BigUint::from_bytes_le(v).into()
            }

            #[allow(dead_code)]
            pub fn to_bytes_le(self) -> Vec<u8> {
                BigUint::to_bytes_le(&self.into())
            }

            #[allow(dead_code)]
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigUint::from(x);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }

            #[allow(dead_code)]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigUint::from(x as u128);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a + b;
                if c > $name::max() {
                    panic!("bounded addition overflow for type {}", stringify!($name));
                }
                c.into()
            }
        }

        /// **Warning**: panics on underflow.
        impl Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a.checked_sub(&b).unwrap_or_else(|| {
                    panic!(
                        "bounded substraction underflow for type {}",
                        stringify!($name)
                    )
                });
                c.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                let c = a * b;
                if c > $name::max() {
                    panic!(
                        "bounded multiplication overflow for type {}",
                        stringify!($name)
                    );
                }
                c.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                if b == BigUint::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a / b;
                c.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Rem for $name {
            type Output = $name;
            fn rem(self, rhs: $name) -> $name {
                let a: BigUint = self.into();
                let b: BigUint = rhs.into();
                if b == BigUint::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a % b;
                c.into()
            }
        }

        impl PartialEq for $name {
            fn eq(&self, rhs: &$name) -> bool {
                let a: BigUint = (*self).into();
                let b: BigUint = (*rhs).into();
                a == b
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &$name) -> Option<std::cmp::Ordering> {
                let a: BigUint = (*self).into();
                let b: BigUint = (*other).into();
                a.partial_cmp(&b)
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl $name {
            /// Returns 2 to the power of the argument
            #[allow(dead_code)]
            pub fn pow2(x: usize) -> $name {
                BigUint::from(1u32).shl(x).into()
            }

            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            pub fn bit(self, i: usize) -> bool {
                assert!(
                    i < self.b.len() * 8,
                    "the bit queried should be lower than the size of the integer representation: {} < {}",
                    i,
                    self.b.len() * 8
                );
                let bigint : BigUint = self.into();
                let tmp: BigUint = bigint >> i;
                (tmp & BigUint::from(1u128)).to_bytes_le()[0] == 1
            }

            #[allow(dead_code)]
            pub fn inv(self, modval: Self) -> Self {
                let biguintmodval : BigUint = modval.into();
                let m = &biguintmodval - BigUint::from(2u32);
                let s: BigUint = (self).into();
                s.modpow(&m, &biguintmodval).into()
            }

            #[allow(dead_code)]
            pub fn pow_felem(self, exp: Self, modval: Self) -> Self {
                let a: BigUint = self.into();
                let b: BigUint = exp.into();
                let m: BigUint = modval.into();
                let c: BigUint = a.modpow(&b, &m);
                c.into()
            }
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u128, modval: Self) -> Self {
                self.pow_felem(BigUint::from(exp).into(), modval)
            }
        }
    };
}
