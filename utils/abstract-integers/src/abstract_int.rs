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

            pub fn max_value() -> Self {
                Self::from(Self::max())
            }

            fn hex_string_to_bytes(s: &str) -> Vec<u8> {
                let s = s.to_string();
                let mut b: Vec<u8> = Vec::new();
                {
                    let mut i = 0;
                    if s.len() % 2 != 0 {
                        i += 1;
                        b.push(u8::from_str_radix(&s[0..1], 16).unwrap());
                    }
                    while i < s.len() {
                        b.push(u8::from_str_radix(&s[i..i + 2], 16).unwrap()); // .expect("Error parsing hex string")
                        i += 2;
                    }
                }
                b
            }

            // TODO -- fix creusot: 'not implemented: 128 bit integers not yet implemented' -- u64 was u128
            #[allow(dead_code)]
            pub fn from_literal(x: u64) -> Self {
                let big_x = BigInt::from(x);
                // if big_x > $name::max().into() {
                //     panic!("literal {} too big for type {}", x, stringify!($name));
                // }
                big_x.into()
            }

            // TODO -- fix creusot: 'not implemented: 128 bit integers not yet implemented' -- u64 was u128
            #[allow(dead_code)]
            pub fn from_signed_literal(x: i64) -> Self {
                let big_x = BigInt::from(x as u64);
                // if big_x > $name::max().into() {
                //     panic!("literal {} too big for type {}", x, stringify!($name));
                // }
                big_x.into()
            }

            /// Returns 2 to the power of the argument
            #[allow(dead_code)]
            pub fn pow2(x: usize) -> $name {
                BigInt::from(1u32).shl(x).into()
            }

            // TODO -- fix creusot: 'unsupported constant expression, try binding this to a variable. See issue #163'
            #[creusot_contracts::trusted]
            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            pub fn bit(self, i: usize) -> bool {
                assert!(
                    i < self.b.as_ref().len() * 8,
                    "the bit queried should be lower than the size of the integer representation: {} < {}",
                    i,
                    self.b.as_ref().len() * 8
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
            #[cfg(feature = "std")]
            fn from(x: BigInt) -> $name {
                // let max_value = Self::max();
                // assert!(x <= max_value, "{} is too large for type {}!", x, stringify!($name));
                let (sign, repr) = x.to_bytes_be();
                // if sign == Sign::Minus && (!$signed) {
                //     panic!("Trying to convert a negative number into an unsigned integer!")
                // }
                // if repr.len() > ($bits + 7) / 8 {
                //     panic!("{} is too large for type {}", x, stringify!($name))
                // }
                let mut out = std::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![
                    0u8;
                    ($bits + 7)
                        / 8
                ])
                .unwrap();
                let upper = out.as_ref().len();
                let lower = upper - repr.len();
                out[lower..upper].copy_from_slice(&repr);
                $name {
                    b: out,
                    sign: sign,
                    signed: $signed,
                }
            }

            #[cfg(not(feature = "std"))]
            fn from(x: BigInt) -> $name {
                // let max_value = Self::max();
                // assert!(x <= max_value, "{} is too large for type {}!", x, stringify!($name));
                let (sign, repr) = x.to_bytes_be();
                // if sign == Sign::Minus && (!$signed) {
                //     panic!("Trying to convert a negative number into an unsigned integer!")
                // }
                // if repr.len() > ($bits + 7) / 8 {
                //     panic!("{} is too large for type {}", x, stringify!($name))
                // }
                let mut out: [u8; ($bits + 7) / 8] =
                    core::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![
                        0u8;
                        ($bits + 7) / 8
                    ])
                    .unwrap();
                let upper = out.as_ref().len();
                let lower = upper - repr.len();
                out[lower..upper].copy_from_slice(&repr);
                $name {
                    b: out,
                    sign: sign,
                    signed: $signed,
                }
            }
        }

        impl Default for $name {
            #[cfg(feature = "std")]
            fn default() -> $name {
                $name {
                    b: std::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![
                        0u8;
                        ($bits + 7)
                            / 8
                    ])
                    .unwrap(),
                    sign: Sign::Plus,
                    signed: $signed,
                }
            }
            #[cfg(not(feature = "std"))]
            fn default() -> $name {
                $name {
                    b: core::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![
                        0u8;
                        ($bits + 7)
                            / 8
                    ])
                    .unwrap(),
                    sign: Sign::Plus,
                    signed: $signed,
                }
            }
        }

        impl Into<BigInt> for $name {
            fn into(self) -> BigInt {
                BigInt::from_bytes_be(self.sign, self.b.as_ref())
            }
        }

        impl Into<BigUint> for $name {
            fn into(self) -> BigUint {
                BigUint::from_bytes_be(self.b.as_ref())
            }
        }

        // #[cfg(feature = "std")]
        // impl std::fmt::Display for $name {
        //     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        //         let uint: BigInt = (*self).into();
        //         write!(f, "{}", uint)
        //     }
        // }
        // #[cfg(not(feature = "std"))]
        // impl core::fmt::Display for $name {
        //     fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        //         let uint: BigInt = (*self).into();
        //         write!(f, "{}", uint)
        //     }
        // }

        // #[cfg(feature = "std")]
        // impl std::fmt::Debug for $name {
        //     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        //         let uint: BigInt = (*self).into();
        //         write!(f, "{}", uint)
        //     }
        // }
        // #[cfg(not(feature = "std"))]
        // impl core::fmt::Debug for $name {
        //     fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        //         let uint: BigInt = (*self).into();
        //         write!(f, "{}", uint)
        //     }
        // }

        // #[cfg(feature = "std")]
        // impl std::fmt::LowerHex for $name {
        //     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        //         let val: BigInt = (*self).into();
        //         std::fmt::LowerHex::fmt(&val, f)
        //     }
        // }
        // #[cfg(not(feature = "std"))]
        // impl core::fmt::LowerHex for $name {
        //     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        //         let val: BigInt = (*self).into();
        //         core::fmt::LowerHex::fmt(&val, f)
        //     }
        // }
    };
}

#[macro_export]
macro_rules! abstract_public {
    ($name:ident) => {
        impl $name {
            #[allow(dead_code)]
            pub fn inv(self, modval: Self) -> Self {
                let biguintmodval: BigInt = modval.into();
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

            // TODO -- fix creusot: 'not implemented: 128 bit integers not yet implemented' -- u64 was u128
            /// Returns self to the power of the argument.
            /// The exponent is a u128.
            #[allow(dead_code)]
            pub fn pow(self, exp: u64, modval: Self) -> Self {
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
                // if c > $name::max() {
                //     panic!("bounded addition overflow for type {}", stringify!($name));
                // }
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
                    a.checked_sub(&b).unwrap() // _or_else(|| {
                                               //     panic!(
                                               //         "bounded substraction underflow for type {}",
                                               //         stringify!($name)
                                               //     )
                                               // })
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
                // if c > $name::max() {
                //     panic!(
                //         "bounded multiplication overflow for type {}",
                //         stringify!($name)
                //     );
                // }
                c.into()
            }
        }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            fn div(self, rhs: $name) -> $name {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                // if b == BigInt::zero() {
                //     panic!("dividing by zero in type {}", stringify!($name));
                // }
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
                // if b == BigInt::zero() {
                //     panic!("dividing by zero in type {}", stringify!($name));
                // }
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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a | b).into()
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a ^ b).into()
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a & b).into()
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            fn shr(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                let b = rhs as usize;
                (a >> b).into()
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            fn shl(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                let b = rhs as usize;
                (a << b).into()
            }
        }

        // TODO : requires equality of bigint in creusot -- 'the trait `creusot_contracts::Model` is not implemented for `hacspec_lib::BigInt`'
        impl PartialEq for $name {
            #[cfg(feature = "std")]
            fn eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { std::cmp::Ordering::Equal => true , _ => false }
            }
            #[cfg(not(feature = "std"))]
            fn eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { core::cmp::Ordering::Equal => true , _ => false }
            }
        }

        impl $name {
            #[cfg(feature = "std")]
            fn is_eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { std::cmp::Ordering::Equal => true , _ => false }
            }
            #[cfg(not(feature = "std"))]
            fn is_eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { core::cmp::Ordering::Equal => true , _ => false }
            }

            fn is_ne(&self, rhs: &$name) -> bool {
               (*self).is_eq(rhs)
            }

            #[cfg(feature = "std")]
            fn is_lt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { std::cmp::Ordering::Less => true , _ => false }
            }
            #[cfg(not(feature = "std"))]
            fn is_lt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { core::cmp::Ordering::Less => true , _ => false }
            }

            #[cfg(feature = "std")]
            fn is_gt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { std::cmp::Ordering::Greater => true , _ => false }
            }
            #[cfg(not(feature = "std"))]
            fn is_gt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) { core::cmp::Ordering::Greater => true , _ => false }
            }
            
            fn is_lte(&self, rhs: &$name) -> bool {
               (*self).is_eq(rhs) || (*self).is_lt(rhs)
            }

            fn is_gte(&self, rhs: &$name) -> bool {
               (*self).is_eq(rhs) || (*self).is_gt(rhs)
            }

        }
        
        impl Eq for $name {}

        impl PartialOrd for $name {
            #[cfg(feature = "std")]
            fn partial_cmp(&self, other: &$name) -> Option<std::cmp::Ordering> {
                Some((*self).cmp(other))
            }
            #[cfg(not(feature = "std"))]
            fn partial_cmp(&self, other: &$name) -> Option<core::cmp::Ordering> {
                Some((*self).cmp(other))
            }
        }

        impl Ord for $name {
            #[cfg(feature = "std")]
            fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                let signed_cmp = (*self).signed.cmp(&(*other).signed);
                match signed_cmp { std::cmp::Ordering::Equal => (), _ => {
                    return signed_cmp;
                }};

                match ((*self).sign, (*rhs).sign) {
                    (Sign::Minus, Sign::Minus) => (*rhs).b.cmp(&(*self).b),
                    (Sign::Minus, _) => std::cmp::Ordering::Less,
                    (Sign::NoSign, Sign::NoSign) => std::cmp::Ordering::Equal,
                    (Sign::Plus, Sign::Plus) => (*self).b.cmp(&(*rhs).b),
                    (Sign::Plus, _) => std::cmp::Ordering::Greater,
                }
            }
            #[cfg(not(feature = "std"))]
            fn cmp(&self, other: &$name) -> core::cmp::Ordering {
                let signed_cmp = (*self).signed.cmp(&(*other).signed);
                match signed_cmp { core::cmp::Ordering::Equal => (), _ => {
                    return signed_cmp;
                }};
                
                match ((*self).sign, (*other).sign) {
                    (Sign::Minus, Sign::Minus) => (*other).b.cmp(&(*self).b),
                    (Sign::Minus, _) => core::cmp::Ordering::Less,
                    (Sign::NoSign, Sign::NoSign) => core::cmp::Ordering::Equal,
                    (Sign::Plus, Sign::Plus) => (*self).b.cmp(&(*other).b),
                    (Sign::Plus, _) => core::cmp::Ordering::Greater,
                    (Sign::NoSign, Sign::Minus) => core::cmp::Ordering::Greater,
                    (Sign::NoSign, Sign::Plus) => core::cmp::Ordering::Less,
                }
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


            #[cfg(feature = "std")]
            #[allow(dead_code)]
            pub fn from_be_bytes(v: &[u8]) -> Self {
                debug_assert!(
                    v.len() <= ($bits + 7) / 8,
                    "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"
                );
                let mut repr = std::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                let upper = repr.as_ref().len();
                let lower = upper - v.len();
                repr[lower..upper].copy_from_slice(&v);
                $name {
                    b: repr,
                    sign: Sign::Plus,
                    signed: false,
                }
            }

            #[cfg(not(feature = "std"))]
            #[allow(dead_code)]
            pub fn from_be_bytes(v: &[u8]) -> Self {
                debug_assert!(
                    v.len() <= ($bits + 7) / 8,
                    "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"
                );
                let mut repr = core::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                let upper = repr.as_ref().len();
                let lower = upper - v.len();
                repr[lower..upper].copy_from_slice(&v);
                $name {
                    b: repr,
                    sign: Sign::Plus,
                    signed: false,
                }
            }

            #[cfg(feature = "std")]
            #[allow(dead_code)]
            pub fn from_le_bytes(v: &[u8]) -> Self {
                debug_assert!(
                    v.len() <= ($bits + 7) / 8,
                    "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"
                );
                let mut repr = std::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                let upper = repr.as_ref().len();
                let lower = upper - v.len();
                repr[lower..upper].copy_from_slice(&v);
                BigInt::from_bytes_le(Sign::Plus, repr.as_ref()).into()
            }
            #[cfg(not(feature = "std"))]
            #[allow(dead_code)]
            pub fn from_le_bytes(v: &[u8]) -> Self {
                debug_assert!(
                    v.len() <= ($bits + 7) / 8,
                    "from_be_bytes: lenght of bytes should be lesser than the lenght of the canvas"
                );
                let mut repr = core::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                let upper = repr.as_ref().len();
                let lower = upper - v.len();
                repr[lower..upper].copy_from_slice(&v);
                BigInt::from_bytes_le(Sign::Plus, repr.as_ref()).into()
            }

            #[allow(dead_code)]
            pub fn to_be_bytes(self) -> [u8; ($bits + 7) / 8] {
                self.b
            }

            #[cfg(feature = "std")]
            #[allow(dead_code)]
            pub fn to_le_bytes(self) -> [u8; ($bits + 7) / 8] {
                let x = BigInt::from_bytes_be(Sign::Plus, self.b.as_ref());
                let (_, x_s) = x.to_bytes_le();
                let mut repr = std::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                repr[0..x_s.len()].copy_from_slice(&x_s);
                repr
            }
            #[cfg(not(feature = "std"))]
            #[allow(dead_code)]
            pub fn to_le_bytes(self) -> [u8; ($bits + 7) / 8] {
                let x = BigInt::from_bytes_be(Sign::Plus, self.b.as_ref());
                let (_, x_s) = x.to_bytes_le();
                let mut repr = core::convert::TryInto::<[u8; ($bits + 7) / 8]>::try_into(vec![0u8; ($bits + 7) / 8]).unwrap();
                repr[0..x_s.len()].copy_from_slice(&x_s);
                repr
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the two arguments are equal and
            /// all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_eq(self, rhs: Self) -> Self {
                if self.is_eq(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the first argument is different from
            /// the second argument, and all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_ne(self, rhs: Self) -> Self {
                if self.is_ne(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the first argument is greater than or
            /// equal to the second argument, and all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_gte(self, rhs: Self) -> Self {
                if self.is_gte(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the first argument is strictly greater
            /// than the second argument, and all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_gt(self, rhs: Self) -> Self {
                if self.is_gt(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the first argument is less than or
            /// equal to the second argument, and all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_lte(self, rhs: Self) -> Self {
                if self.is_lte(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

            // TODO : dependency on 'from_literal'
            /// Produces a new integer which is all ones if the first argument is strictly less than
            /// the second argument, and all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_lt(self, rhs: Self) -> Self {
                if self.is_lt(&rhs) {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
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
                    _ => panic!("from_hex requires the first argument to be + or -"),
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
            pub fn declassify(self) -> BigInt {
                self.into()
            }

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
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a | b).into()
            }
        }

        impl BitXor for $name {
            type Output = $name;
            fn bitxor(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a ^ b).into()
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            fn bitand(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a & b).into()
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            fn shr(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                (a >> rhs).into()
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            fn shl(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                (a << rhs).into()
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
