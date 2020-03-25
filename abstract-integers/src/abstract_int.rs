#[macro_export]
macro_rules! abstract_int {
    ($name:ident, $bits:literal, $signed:literal) => {
        #[derive(Clone, Copy)]
        pub struct $name {
            b: [u8; ($bits + 7) / 8],
            sign: Sign,
            signed: bool,
        }

        impl $name {
            fn max() -> BigInt {
                BigInt::from(1u32).shl($bits) - BigInt::one()
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
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigInt::from(x);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }

            #[allow(dead_code)]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigInt::from(x as u128);
                if big_x > $name::max().into() {
                    panic!("literal {} too big for type {}", x, stringify!($name));
                }
                big_x.into()
            }

            /// Returns 2 to the power of the argument
            #[allow(dead_code)]
            pub fn pow2(x: usize) -> $name {
                BigInt::from(1u32).shl(x).into()
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
                let bigint : BigInt = self.into();
                let tmp: BigInt = bigint >> i;
                (tmp & BigInt::one()).to_bytes_le().1[0] == 1
            }
        }

        impl From<BigUint> for $name {
            fn from(x: BigUint) -> $name {
                Self::from(BigInt::from(x))
            }
        }

        impl From<BigInt> for $name {
            fn from(x: BigInt) -> $name {
                let max_value = Self::max();
                assert!(x < max_value, "{} is too large for type {}!", x, stringify!($name));
                let repr = x.to_bytes_be().1;
                if repr.len() > ($bits + 7) / 8 {
                    panic!("{} is too large for type {}", x, stringify!($name))
                }
                let mut out = [0u8; ($bits + 7) / 8];
                let upper = out.len();
                let lower = upper - repr.len();
                out[lower..upper].copy_from_slice(&repr);
                $name {
                    b: out,
                    sign: Sign::Plus,
                    signed: $signed,
                }
            }
        }

        impl Default for $name {
            fn default() -> $name {
                $name {
                    b: [0u8; ($bits + 7) / 8],
                    sign: Sign::Plus,
                    signed: $signed,
                }
            }
        }

        impl Into<BigInt> for $name {
            fn into(self) -> BigInt {
                BigInt::from_bytes_be(self.sign, &self.b)
            }
        }

        impl Into<BigUint> for $name {
            fn into(self) -> BigUint {
                BigUint::from_bytes_be(&self.b)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigInt = (*self).into();
                write!(f, "{}", uint)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let uint: BigInt = (*self).into();
                write!(f, "{}", uint)
            }
        }
    };
}

#[macro_export]
macro_rules! abstract_public {
    ($name:ident) => {
        impl $name {
            #[allow(dead_code)]
            pub fn inv(self, modval: Self) -> Self {
                let biguintmodval : BigInt = modval.into();
                let m = &biguintmodval - BigInt::from(2u32);
                let s: BigInt = (self).into();
                s.modpow(&m, &biguintmodval).into()
            }

            #[allow(dead_code)]
            pub fn pow_felem(self, exp: Self, modval: Self) -> Self {
                let a: BigInt = self.into();
                let b: BigInt = exp.into();
                let m: BigInt = modval.into();
                let c: BigInt = a.modpow(&b, &m);
                c.into()
            }
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u128, modval: Self) -> Self {
                self.pow_felem(BigInt::from(exp).into(), modval)
            }

            fn rem(self, n: Self) -> Self {
                self % n
            }
        }

        /// **Warning**: panics on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                let c = if self.signed {
                    a - b
                } else {
                    a.checked_sub(&b).unwrap_or_else(|| {
                        panic!(
                            "bounded substraction underflow for type {}",
                            stringify!($name)
                        )
                    })
                };
                c.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                if b == BigInt::zero() {
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                if b == BigInt::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a % b;
                c.into()
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

        impl PartialEq for $name {
            fn eq(&self, rhs: &$name) -> bool {
                let a: BigInt = (*self).into();
                let b: BigInt = (*rhs).into();
                a == b
            }
        }

        impl Eq for $name {}

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &$name) -> Option<std::cmp::Ordering> {
                let a: BigInt = (*self).into();
                let b: BigInt = (*other).into();
                a.partial_cmp(&b)
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                self.partial_cmp(other).unwrap()
            }
        }
    };
}

#[macro_export]
macro_rules! abstract_unsigned {
    ($name:ident, $bits:literal) => {
        abstract_int!($name, $bits, false);

        impl $name {
            #[allow(dead_code)]
            pub fn from_hex(s: &str) -> Self {
                BigInt::from_bytes_be(Sign::Plus, &Self::hex_string_to_bytes(s)).into()
            }

            #[allow(dead_code)]
            pub fn from_bytes_le(v: &[u8]) -> Self {
                BigInt::from_bytes_le(Sign::Plus, v).into()
            }

            #[allow(dead_code)]
            pub fn to_bytes_le(self) -> Vec<u8> {
                BigInt::to_bytes_le(&self.into()).1
            }
        }
    };
}


#[macro_export]
macro_rules! abstract_signed {
    ($name:ident, $bits:literal) => {
        abstract_int!($name, $bits, true);

        impl $name {
            #[allow(dead_code)]
            pub fn from_hex(sign: &str, s: &str) -> Self {
                let sign = match sign {
                    "+" => Sign::Plus,
                    "-" => Sign::Minus,
                    "" => Sign::NoSign,
                    _ => panic!("from_hex requires the first argument to be + or -")
                };
                BigInt::from_bytes_be(sign, &Self::hex_string_to_bytes(s)).into()
            }
        }
    };
}

#[macro_export]
macro_rules! abstract_unsigned_public_integer {
    ($name:ident, $bits:literal) => {
        abstract_unsigned!($name, $bits);
        abstract_public!($name);
    };
}

#[macro_export]
macro_rules! abstract_signed_public_integer {
    ($name:ident, $bits:literal) => {
        abstract_signed!($name, $bits);
        abstract_public!($name);
    };
}

// FIXME: Implement ct algorithms.
#[macro_export]
macro_rules! abstract_secret {
    ($name:ident, $bits:literal) => {
        impl $name {
            fn rem(self, n: Self) -> Self {
                let a: BigInt = self.into();
                let b: BigInt = n.into();
                if b == BigInt::zero() {
                    panic!("dividing by zero in type {}", stringify!($name));
                }
                let c = a % b;
                c.into()
            }
        }

        /// **Warning**: panics on overflow.
        impl Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
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
macro_rules! abstract_unsigned_secret_integer {
    ($name:ident, $bits:literal) => {
        abstract_unsigned!($name, $bits);
        abstract_secret!($name, $bits);
    };
}

#[macro_export]
macro_rules! abstract_signed_secret_integer {
    ($name:ident, $bits:literal) => {
        abstract_signed!($name, $bits);
        abstract_secret!($name, $bits);
    };
}

// ============ Legacy API ============

/// Defines a bounded natural integer with regular arithmetic operations, checked for overflow
/// and underflow.
#[macro_export]
macro_rules! define_abstract_integer_checked {
    ($name:ident, $bits:literal) => {
        abstract_unsigned_public_integer!($name, $bits);
    };
}
