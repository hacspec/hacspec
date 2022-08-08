// use creusot_contracts::*;

#[macro_export]
macro_rules! abstract_int {
    ($name:ident, $bits:literal, $signed:literal) => {
        #[derive(Clone, Copy)]
        pub struct $name {
            b: [u8; ($bits + 7) / 8],
            sign: Sign,
            signed: bool,
        }

        #[cfg(feature = "contracts")]
        #[cfg(not(feature = "hacspec"))]
        impl Model for $name {
            type ModelTy = Int;

            #[logic]
            fn model(self) -> Self::ModelTy {
                pearlite! { absurd }
                // 0 // TODO
            }
        }

        // #[cfg(feature = "contracts")]
        // #[cfg(not(feature = "hacspec"))]
        // impl OrdLogic for $name {
        //     #[logic]
        //     fn cmp_log(self : Self, b : Self) -> Ordering { Ordering::Equal }
        //     #[logic]
        //     fn cmp_le_log(a : Self, b : Self) { }
        //     #[logic]
        //     fn cmp_lt_log(a : Self, b : Self) { }
        //     #[logic]
        //     fn cmp_ge_log(a : Self, b : Self) { }
        //     #[logic]
        //     fn cmp_gt_log(a : Self, b : Self) { }
        //     #[logic]
        //     fn refl(a : Self) { }
        //     #[logic]
        //     fn trans(a : Self, b : Self, c : Self, d : Ordering) { }
        //     #[logic]
        //     fn antisym1(a : Self, b : Self) { }
        //     #[logic]
        //     fn antisym2(a : Self, b : Self) { }
        //     #[logic]
        //     fn eq_cmp(a : Self, b : Self) { }
        // }

        impl $name {
            #[trusted]
            fn max() -> BigInt {
                BigInt::from(1u32).shl($bits) - BigInt::one()
            }

            pub fn max_value() -> Self {
                Self::from(Self::max())
            }

            #[trusted]
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

            #[allow(dead_code)]
            #[trusted]
            pub fn from_literal(x: u128) -> Self {
                let big_x = BigInt::from(x);
                // if big_x > $name::max().into() {
                //     panic!("literal {} too big for type {}", x, stringify!($name));
                // }
                big_x.into()
            }

            #[allow(dead_code)]
            #[trusted]
            pub fn from_signed_literal(x: i128) -> Self {
                let big_x = BigInt::from(x as u128);
                // if big_x > $name::max().into() {
                //     panic!("literal {} too big for type {}", x, stringify!($name));
                // }
                big_x.into()
            }

            /// Returns 2 to the power of the argument
            #[allow(dead_code)]
            #[trusted]
            pub fn pow2(x: usize) -> $name {
                BigInt::from(1u32).shl(x).into()
            }

            /// Gets the `i`-th least significant bit of this integer.
            #[allow(dead_code)]
            #[trusted]
            pub fn bit(self, i: usize) -> bool {
                // assert!(
                //     i < self.b.as_ref().len() * 8,
                //     "the bit queried should be lower than the size of the integer representation: {} < {}",
                //     i,
                //     self.b.as_ref().len() * 8
                // );
                let bigint: BigInt = self.into();
                let tmp: BigInt = bigint >> i;
                (tmp & BigInt::one()).to_bytes_le().1[0] == 1
            }
        }

        impl From<BigUint> for $name {
            #[trusted]
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
            #[trusted]
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
            #[trusted]
            fn into(self) -> BigInt {
                BigInt::from_bytes_be(self.sign, self.b.as_ref())
            }
        }

        impl Into<BigUint> for $name {
            #[trusted]
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
            #[trusted]
            pub fn inv(self, modval: Self) -> Self {
                let biguintmodval: BigInt = modval.into();
                let m = &biguintmodval - BigInt::from(2u32);
                let s: BigInt = (self).into();
                s.modpow(&m, &biguintmodval).into()
            }

            #[allow(dead_code)]
            #[trusted]
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
            #[trusted]
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
            #[trusted]
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
            #[trusted]
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

        // /// **Warning**: panics on overflow.
        // impl Mul for $name {
        //     type Output = $name;

        //     #[trusted]
        //     fn mul(self, rhs: $name) -> $name {
        //         let a: BigInt = self.into();
        //         let b: BigInt = rhs.into();
        //         let c = a * b;
        //         // if c > $name::max() {
        //         //     panic!(
        //         //         "bounded multiplication overflow for type {}",
        //         //         stringify!($name)
        //         //     );
        //         // }
        //         c.into()
        //     }
        // }

        /// **Warning**: panics on division by 0.
        impl Div for $name {
            type Output = $name;
            #[trusted]
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
            #[trusted]
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
            #[trusted]
            fn bitor(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a | b).into()
            }
        }

        impl BitXor for $name {
            type Output = $name;
            #[trusted]
            fn bitxor(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a ^ b).into()
            }
        }

        impl BitAnd for $name {
            type Output = $name;
            #[trusted]
            fn bitand(self, rhs: Self) -> Self::Output {
                let a: BigInt = self.into();
                let b: BigInt = rhs.into();
                (a & b).into()
            }
        }

        impl Shr<usize> for $name {
            type Output = $name;
            #[trusted]
            fn shr(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                let b = rhs as usize;
                (a >> b).into()
            }
        }

        impl Shl<usize> for $name {
            type Output = $name;
            #[trusted]
            fn shl(self, rhs: usize) -> Self::Output {
                let a: BigInt = self.into();
                let b = rhs as usize;
                (a << b).into()
            }
        }

        impl $name {
            #[cfg(feature = "std")]
            fn ord_cmp(&self, other: &$name) -> std::cmp::Ordering {
                let signed_cmp = (*self).signed.cmp(&(*other).signed);
                match signed_cmp {
                    std::cmp::Ordering::Equal => (),
                    _ => {
                        return signed_cmp;
                    }
                };

                match ((*self).sign, (*rhs).sign) {
                    (Sign::Minus, Sign::Minus) => (*rhs).b.cmp(&(*self).b),
                    (Sign::Minus, _) => std::cmp::Ordering::Less,
                    (Sign::NoSign, Sign::NoSign) => std::cmp::Ordering::Equal,
                    (Sign::Plus, Sign::Plus) => (*self).b.cmp(&(*rhs).b),
                    (Sign::Plus, _) => std::cmp::Ordering::Greater,
                }
            }
            #[cfg(not(feature = "std"))]
            fn ord_cmp(&self, other: &$name) -> core::cmp::Ordering {
                let signed_cmp = if (*self).signed {
                    if (*other).signed {
                        core::cmp::Ordering::Equal
                    } else {
                        core::cmp::Ordering::Greater
                    }
                } else {
                    if (*other).signed {
                        core::cmp::Ordering::Less
                    } else {
                        core::cmp::Ordering::Equal
                    }
                };

                match signed_cmp {
                    core::cmp::Ordering::Equal => (),
                    _ => {
                        return signed_cmp;
                    }
                };

                match ((*self).sign, (*other).sign) {
                    (Sign::Minus, Sign::Minus) => {
                        let mut i = 0;
                        while i < (256 + 7) / 8 {
                            let compare = (*other).b[i].cmp(&(*self).b[i]);
                            if compare != core::cmp::Ordering::Equal {
                                return compare;
                            }
                            i += 1;
                        }
                        core::cmp::Ordering::Equal
                    }
                    (Sign::Minus, _) => core::cmp::Ordering::Less,
                    (Sign::NoSign, Sign::NoSign) => core::cmp::Ordering::Equal,
                    (Sign::Plus, Sign::Plus) => {
                        let mut i = 0;
                        while i < (256 + 7) / 8 {
                            let compare = (*self).b[i].cmp(&(*other).b[i]);
                            if compare != core::cmp::Ordering::Equal {
                                return compare;
                            }
                            i += 1;
                        }
                        core::cmp::Ordering::Equal
                    }
                    (Sign::Plus, _) => core::cmp::Ordering::Greater,
                    (Sign::NoSign, Sign::Minus) => core::cmp::Ordering::Greater,
                    (Sign::NoSign, Sign::Plus) => core::cmp::Ordering::Less,
                }
            }
        }
        // TODO : requires equality of bigint in creusot -- 'the trait `creusot_contracts::Model` is not implemented for `hacspec_lib::BigInt`'
        impl PartialEq for $name {
            #[cfg(feature = "std")]
            fn eq(&self, rhs: &$name) -> bool {
                match (*self).ord_cmp(rhs) {
                    std::cmp::Ordering::Equal => true,
                    _ => false,
                }
            }
            #[cfg(not(feature = "std"))]
            fn eq(&self, rhs: &$name) -> bool {
                match (*self).ord_cmp(rhs) {
                    core::cmp::Ordering::Equal => true,
                    _ => false,
                }
            }
        }

        impl $name {
            #[cfg(feature = "std")]
            fn is_eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    std::cmp::Ordering::Equal => true,
                    _ => false,
                }
            }
            #[cfg(not(feature = "std"))]
            fn is_eq(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    core::cmp::Ordering::Equal => true,
                    _ => false,
                }
            }

            fn is_ne(&self, rhs: &$name) -> bool {
                (*self).is_eq(rhs)
            }

            #[cfg(feature = "std")]
            fn is_lt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    std::cmp::Ordering::Less => true,
                    _ => false,
                }
            }
            #[cfg(not(feature = "std"))]
            fn is_lt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    core::cmp::Ordering::Less => true,
                    _ => false,
                }
            }

            #[cfg(feature = "std")]
            fn is_gt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    std::cmp::Ordering::Greater => true,
                    _ => false,
                }
            }
            #[cfg(not(feature = "std"))]
            fn is_gt(&self, rhs: &$name) -> bool {
                match (*self).cmp(rhs) {
                    core::cmp::Ordering::Greater => true,
                    _ => false,
                }
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
                Some((*self).ord_cmp(other))
            }
            #[cfg(not(feature = "std"))]
            fn partial_cmp(&self, other: &$name) -> Option<core::cmp::Ordering> {
                Some((*self).ord_cmp(other))
            }
        }

        impl Ord for $name {
            #[cfg(feature = "std")]
            fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                self.ord_cmp(other)
            }
            #[cfg(not(feature = "std"))]
            fn cmp(&self, other: &$name) -> core::cmp::Ordering {
                self.ord_cmp(other)
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
            #[trusted]
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
            #[trusted]
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

            /// Produces a new integer which is all ones if the two arguments are equal and
            /// all zeroes otherwise.
            /// **NOTE:** This is not constant time but `BigInt` generally isn't.
            #[inline]
            pub fn comp_eq(self, rhs: Self) -> Self {
                if self == rhs {
                    let one = Self::from_literal(1);
                    (one << ($bits - 1)) - one
                } else {
                    Self::default()
                }
            }

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
