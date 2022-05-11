// #![feature(array_chunks)]
// #![feature(prelude_import)]
// #[prelude_import]
// use std::prelude::rust_2018::*;
// #[macro_use]
// extern crate std;
#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

pub use hacspec_lib::*;

#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;


#[cfg(not(feature = "hacspec"))]
pub use creusot_contracts::*;

// const a = String::from("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed");

// #[cfg(feature = "hacspec")]
public_nat_mod!(
    type_name: Ed25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

// #[cfg(not(feature = "hacspec"))]
// #[derive(Clone, Copy)]
// pub struct FieldCanvas {
//     b: [u8; (256 + 7) / 8],
//     sign: Sign,
//     signed: bool,
// }

// use std::convert::TryInto;
// impl Default for FieldCanvas {
//     fn default() -> FieldCanvas {
//         let res = FieldCanvas {
//             b: vec![0u8; 32].try_into().unwrap(),
//             sign: Sign::Plus,
//             signed: false,
//         };
//         res.b;
//         res.sign;
//         res.signed;
//         res        
//     }
// }

// impl FieldCanvas {
//     fn max() -> BigInt {
//         BigInt::from(1u32).shl(256) - BigInt::one()
//     }

//     pub fn max_value() -> Self {
//         Self::from(Self::max())
//     }

//     // fn hex_string_to_bytes(s: &str) -> Vec<u8> {
//     //     let s = if s.len() % 2 != 0 {
//     //         let mut x = "0".to_string();
//     //         x.push_str(s);
//     //         x
//     //     } else {
//     //         s.to_string()
//     //     };
//     //     // assert!(s.len() % 2 == 0, "length of hex string {}: {}",s, s.len());
//     //     let b: Result<Vec<u8>, ParseIntError> = (0..s.len())
//     //         .step_by(2)
//     //         .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
//     //         .collect();
//     //     b.expect("Error parsing hex string")
//     // }

//     // not implemented: 128 bit integers not yet implemented
//     // #[allow(dead_code)]
//     // pub fn from_literal(x: u128) -> Self {
//     //     let big_x = BigInt::from(x);
//     //     if big_x > FieldCanvas::max().into() {
//     //         panic!("literal {} too big for type {}", x, stringify!(FieldCanvas));
//     //     }
//     //     big_x.into()
//     // }

//     // #[allow(dead_code)]
//     // pub fn from_signed_literal(x: i128) -> Self {
//     //     let big_x = BigInt::from(x as u128);
//     //     if big_x > FieldCanvas::max().into() {
//     //         panic!("literal {} too big for type {}", x, stringify!(FieldCanvas));
//     //     }
//     //     big_x.into()
//     // }

//     /// Returns 2 to the power of the argument
//     #[allow(dead_code)]
//     pub fn pow2(x: usize) -> FieldCanvas {
//         BigInt::from(1u32).shl(x).into()
//     }

//     /// Gets the `i`-th least significant bit of this integer.
//     #[allow(dead_code)]
//     pub fn bit(self, i: usize) -> bool {
//         // assert!(
//         //     i < self.b.len() * 8,
//         //     "the bit queried should be lower than the size of the integer representation: {} < {}",
//         //     i,
//         //     self.b.len() * 8
//         // );
//         let bigint : BigInt = self.into();
//         let tmp: BigInt = bigint >> i;
//         (tmp & BigInt::one()).to_bytes_le().1[0] == 1
//     }
// }

// impl From<BigUint> for FieldCanvas {
//     fn from(x: BigUint) -> FieldCanvas {
//         Self::from(BigInt::from(x))
//     }
// }

// impl From<BigInt> for FieldCanvas {
//     fn from(x: BigInt) -> FieldCanvas {
//         // let max_value = Self::max();
//         // assert!(x <= max_value, "{} is too large for type {}!", x, stringify!(FieldCanvas));
//         let (sign, repr) = x.to_bytes_be();
//         // if sign == Sign::Minus && (!false) {
//         //     panic!("Trying to convert a negative number into an unsigned integer!")
//         // }
//         // if repr.len() > (256 + 7) / 8 {
//         //     panic!("{} is too large for type {}", x, stringify!(FieldCanvas))
//         // }
//         let mut out : [u8; (256 + 7) / 8] = vec![0u8; 32].try_into().unwrap(); // = [0u8; (256 + 7) / 8];
//         let upper = (256 + 7) / 8; // out.len();
//         let lower = upper - repr.len();
//         out[lower..upper].copy_from_slice(&repr);
        
//         FieldCanvas {
//             b: out,
//             sign: sign,
//             signed: false,
//         }
//     }
// }

// impl Into<BigInt> for FieldCanvas {
//     fn into(self) -> BigInt {
//         BigInt::from_bytes_be(self.sign, self.b.as_ref())
//     }
// }

// impl Into<BigUint> for FieldCanvas {
//     fn into(self) -> BigUint {
//         BigUint::from_bytes_be(self.b.as_ref())
//     }
// }

// // #[cfg(feature = "std")]
// // impl std::fmt::Display for FieldCanvas {
// //     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
// //         let uint: BigInt = (*self).into();
// //         write!(f, "{}", uint)
// //     }
// // }
// // #[cfg(not(feature = "std"))]
// // impl core::fmt::Display for FieldCanvas {
// //     fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
// //         let uint: BigInt = (*self).into();
// //         write!(f, "{}", uint)
// //     }
// // }

// // #[cfg(feature = "std")]
// // impl std::fmt::Debug for FieldCanvas {
// //     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
// //         let uint: BigInt = (*self).into();
// //         write!(f, "{}", uint)
// //     }
// // }
// // #[cfg(not(feature = "std"))]
// // impl core::fmt::Debug for FieldCanvas {
// //     fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
// //         let uint: BigInt = (*self).into();
// //         write!(f, "{}", uint)
// //     }
// // }

// // #[cfg(feature = "std")]
// // impl std::fmt::LowerHex for FieldCanvas {
// //     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
// //         let val: BigInt = (*self).into();
// //         std::fmt::LowerHex::fmt(&val, f)
// //     }
// // }
// // #[cfg(not(feature = "std"))]
// // impl core::fmt::LowerHex for FieldCanvas {
// //     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
// //         let val: BigInt = (*self).into();
// //         core::fmt::LowerHex::fmt(&val, f)
// //     }
// // }


// impl FieldCanvas {
//     #[allow(dead_code)]
//     pub fn inv(self, modval: Self) -> Self {
//         let biguintmodval: BigInt = modval.into();
//         let m = &biguintmodval - BigInt::from(2u32);
//         let s: BigInt = (self).into();
//         s.modpow(&m, &biguintmodval).into()
//     }

//     #[allow(dead_code)]
//     pub fn pow_felem(self, exp: Self, modval: Self) -> Self {
//         let a: BigInt = self.into();
//         let b: BigInt = exp.into();
//         let m: BigInt = modval.into();
//         let c: BigInt = a.modpow(&b, &m);
//         c.into()
//     }
//     /// Returns self to the power of the argument.
//     /// The exponent is a u128.
//     #[allow(dead_code)]
//     pub fn pow(self, exp: u128, modval: Self) -> Self {
//         self.pow_felem(BigInt::from(exp).into(), modval)
//     }

//     fn rem(self, n: Self) -> Self {
//         self % n
//     }
// }

// /// **Warning**: panics on overflow.
// impl Add for FieldCanvas {
//     type Output = FieldCanvas;
//     fn add(self, rhs: FieldCanvas) -> FieldCanvas {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         let c = a + b;
//         if c > FieldCanvas::max() {
//             panic!("bounded addition overflow for type {}", stringify!(FieldCanvas));
//         }
//         c.into()
//     }
// }

// /// **Warning**: panics on underflow.
// impl Sub for FieldCanvas {
//     type Output = FieldCanvas;
//     fn sub(self, rhs: FieldCanvas) -> FieldCanvas {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         let c = if self.signed {
//             a - b
//         } else {
//             a.checked_sub(&b).unwrap_or_else(|| {
//                 panic!(
//                     "bounded substraction underflow for type {}",
//                     stringify!(FieldCanvas)
//                 )
//             })
//         };
//         c.into()
//     }
// }

// /// **Warning**: panics on overflow.
// impl Mul for FieldCanvas {
//     type Output = FieldCanvas;
//     fn mul(self, rhs: FieldCanvas) -> FieldCanvas {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         let c = a * b;
//         if c > FieldCanvas::max() {
//             panic!(
//                 "bounded multiplication overflow for type {}",
//                 stringify!(FieldCanvas)
//             );
//         }
//         c.into()
//     }
// }

// /// **Warning**: panics on division by 0.
// impl Div for FieldCanvas {
//     type Output = FieldCanvas;
//     fn div(self, rhs: FieldCanvas) -> FieldCanvas {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         if b == BigInt::zero() {
//             panic!("dividing by zero in type {}", stringify!(FieldCanvas));
//         }
//         let c = a / b;
//         c.into()
//     }
// }

// /// **Warning**: panics on division by 0.
// impl Rem for FieldCanvas {
//     type Output = FieldCanvas;
//     fn rem(self, rhs: FieldCanvas) -> FieldCanvas {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         if b == BigInt::zero() {
//             panic!("dividing by zero in type {}", stringify!(FieldCanvas));
//         }
//         let c = a % b;
//         c.into()
//     }
// }

// impl Not for FieldCanvas {
//     type Output = FieldCanvas;
//     fn not(self) -> Self::Output {
//         unimplemented!();
//     }
// }

// impl BitOr for FieldCanvas {
//     type Output = FieldCanvas;
//     fn bitor(self, rhs: Self) -> Self::Output {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         (a | b).into()
//     }
// }

// impl BitXor for FieldCanvas {
//     type Output = FieldCanvas;
//     fn bitxor(self, rhs: Self) -> Self::Output {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         (a ^ b).into()
//     }
// }

// impl BitAnd for FieldCanvas {
//     type Output = FieldCanvas;
//     fn bitand(self, rhs: Self) -> Self::Output {
//         let a: BigInt = self.into();
//         let b: BigInt = rhs.into();
//         (a & b).into()
//     }
// }

// impl Shr<usize> for FieldCanvas {
//     type Output = FieldCanvas;
//     fn shr(self, rhs: usize) -> Self::Output {
//         let a: BigInt = self.into();
//         let b = rhs as usize;
//         (a >> b).into()
//     }
// }

// impl Shl<usize> for FieldCanvas {
//     type Output = FieldCanvas;
//     fn shl(self, rhs: usize) -> Self::Output {
//         let a: BigInt = self.into();
//         let b = rhs as usize;
//         (a << b).into()
//     }
// }

// impl PartialEq for FieldCanvas {
//     fn eq(&self, rhs: &FieldCanvas) -> bool {
//         let a: BigInt = (*self).into();
//         let b: BigInt = (*rhs).into();
//         a == b
//     }
// }

// impl Eq for FieldCanvas {}

// impl PartialOrd for FieldCanvas {
//     #[cfg(feature = "std")]
//     fn partial_cmp(&self, other: &FieldCanvas) -> Option<std::cmp::Ordering> {
//         let a: BigInt = (*self).into();
//         let b: BigInt = (*other).into();
//         a.partial_cmp(&b)
//     }
//     #[cfg(not(feature = "std"))]
//     fn partial_cmp(&self, other: &FieldCanvas) -> Option<core::cmp::Ordering> {
//         let a: BigInt = (*self).into();
//         let b: BigInt = (*other).into();
//         a.partial_cmp(&b)
//     }
// }

// impl Ord for FieldCanvas {
//     #[cfg(feature = "std")]
//     fn cmp(&self, other: &FieldCanvas) -> std::cmp::Ordering {
//         self.partial_cmp(other).unwrap()
//     }
//     #[cfg(not(feature = "std"))]
//     fn cmp(&self, other: &FieldCanvas) -> core::cmp::Ordering {
//         self.partial_cmp(other).unwrap()
//     }
// }



// impl FieldCanvas {
//     #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
//     pub fn from_byte_seq_be<A: SeqTrait<U8>>(s: &A) -> FieldCanvas {
//         FieldCanvas::from_be_bytes(
//             s.iter()
//                 .map(|x| U8::declassify(*x))
//                 .collect::<Vec<_>>()
//                 .as_slice(),
//         )
//     }

//     #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
//     pub fn from_public_byte_seq_be<A: SeqTrait<u8>>(s: A) -> FieldCanvas {
//         // XXX: unnecessarily complex
//         FieldCanvas::from_be_bytes(s.iter().map(|x| *x).collect::<Vec<_>>().as_slice())
//     }

//     #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
//     pub fn to_byte_seq_be(self) -> hacspec_lib::Seq<U8> {
//         hacspec_lib::Seq::from_vec(
//             self.to_be_bytes()
//                 .iter()
//                 .map(|x| U8::classify(*x))
//                 .collect::<Vec<U8>>(),
//         )
//     }
// }

// // impl NumericCopy for FieldCanvas {}
// impl UnsignedInteger for FieldCanvas {}
// // impl UnsignedIntegerCopy for FieldCanvas {}
// impl Integer for FieldCanvas {
//     const NUM_BITS: usize = 256;

//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn ZERO() -> Self {
//         Self::from_literal(0)
//     }
//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn ONE() -> Self {
//         Self::from_literal(1)
//     }
//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn TWO() -> Self {
//         Self::from_literal(2)
//     }

//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn from_literal(val: u128) -> Self {
//         Self::from_literal(val)
//     }

//     #[inline]
//     #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
//     fn from_hex_string(s: &String) -> Self {
//         Self::from_hex(&s.replace("0x", ""))
//     }

//     /// Get bit `i` of this integer.
//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn get_bit(self, i: usize) -> Self {
//         (self >> i) & Self::ONE()
//     }

//     /// Set bit `i` of this integer to `b` and return the result.
//     /// Bit `b` has to be `0` or `1`.
//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn set_bit(self, b: Self, i: usize) -> Self {
//         debug_assert!(b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO()));
//         let tmp1 = Self::from_literal(!(1 << i));
//         let tmp2 = b << i;
//         (self & tmp1) | tmp2
//     }

//     /// Set bit `pos` of this integer to bit `yi` of integer `y`.
//     #[inline]
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn set(self, pos: usize, y: Self, yi: usize) -> Self {
//         let b = y.get_bit(yi);
//         self.set_bit(b, pos)
//     }

//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn rotate_left(self, n: usize) -> Self {
//         // Taken from https://blog.regehr.org/archives/1063
//         assert!(n < Self::NUM_BITS);
//         (self.clone() << n) | (self >> ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
//     }

//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn rotate_right(self, n: usize) -> Self {
//         // Taken from https://blog.regehr.org/archives/1063
//         assert!(n < Self::NUM_BITS);
//         (self.clone() >> n) | (self << ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
//     }
// }
// impl ModNumeric for FieldCanvas {
//     /// (self - rhs) % n.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn sub_mod(self, rhs: Self, n: Self) -> Self {
//         (self - rhs) % n
//     }
//     /// `(self + rhs) % n`
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn add_mod(self, rhs: Self, n: Self) -> Self {
//         (self + rhs) % n
//     }
//     /// `(self * rhs) % n`
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn mul_mod(self, rhs: Self, n: Self) -> Self {
//         (self * rhs) % n
//     }
//     /// `(self ^ exp) % n`
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn pow_mod(self, exp: Self, n: Self) -> Self {
//         self.pow_felem(exp, n)
//     }
//     /// `self % n`
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn modulo(self, n: Self) -> Self {
//         self % n
//     }
//     /// `self % n` that always returns a positive integer
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn signed_modulo(self, n: Self) -> Self {
//         self.modulo(n)
//     }
//     /// `|self|`
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn absolute(self) -> Self {
//         self
//     }
// }
// impl Numeric for FieldCanvas {
//     /// Return largest value that can be represented.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn max_val() -> Self {
//         FieldCanvas::max_value()
//     }

//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn wrap_add(self, rhs: Self) -> Self {
//         self + rhs
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn wrap_sub(self, rhs: Self) -> Self {
//         self - rhs
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn wrap_mul(self, rhs: Self) -> Self {
//         self * rhs
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn wrap_div(self, rhs: Self) -> Self {
//         self / rhs
//     }

//     /// `self ^ exp` where `exp` is a `u32`.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn exp(self, exp: u32) -> Self {
//         self.pow(exp.into(), Self::max_val())
//     }
//     /// `self ^ exp` where `exp` is a `Self`.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn pow_self(self, exp: Self) -> Self {
//         self.pow_felem(exp.into(), Self::max_val())
//     }
//     /// Division.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn divide(self, rhs: Self) -> Self {
//         self / rhs
//     }
//     /// Invert self modulo n.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn inv(self, n: Self) -> Self {
//         FieldCanvas::inv(self, n)
//     }

//     // Comparison functions returning bool.
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn equal(self, other: Self) -> bool {
//         self == other
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn greater_than(self, other: Self) -> bool {
//         self > other
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn greater_than_or_qual(self, other: Self) -> bool {
//         self >= other
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn less_than(self, other: Self) -> bool {
//         self < other
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn less_than_or_equal(self, other: Self) -> bool {
//         self >= other
//     }

//     // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn not_equal_bm(self, other: Self) -> Self {
//         if !self.equal(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn equal_bm(self, other: Self) -> Self {
//         if self.equal(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn greater_than_bm(self, other: Self) -> Self {
//         if self.greater_than(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn greater_than_or_equal_bm(self, other: Self) -> Self {
//         if self.greater_than_or_qual(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn less_than_bm(self, other: Self) -> Self {
//         if self.less_than(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
//     #[cfg_attr(feature = "use_attributes", in_hacspec)]
//     fn less_than_or_equal_bm(self, other: Self) -> Self {
//         if self.less_than_or_equal(other) {
//             Self::max_val()
//         } else {
//             Self::from_literal(0)
//         }
//     }
// }

// pub struct Ed25519FieldElement(FieldCanvas);

// // TODO: implement PartialEq, Eq, PartialOrd, Ord,
// impl PartialOrd for Ed25519FieldElement {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         Some(self.cmp(other))
//     }
// }
// impl Ord for Ed25519FieldElement {
//     fn cmp(&self, other: &Self) -> Ordering {
//         self.0.cmp(&other.0)
//     }
// }
// impl PartialEq for Ed25519FieldElement {
//     fn eq(&self, other: &Self) -> bool {
//         self.0 == other.0
//     }
// }
// impl Eq for Ed25519FieldElement {}

// /// **Warning**: wraps on overflow.
// impl Add for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn add(self, rhs: Ed25519FieldElement) -> Ed25519FieldElement {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         let a: BigUint = a.into();
//         let b: BigUint = b.into();
//         let c: BigUint = a + b;
//         let max: BigUint = FieldCanvas::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").into();
//         let d: BigUint = c % max;
//         let d: FieldCanvas = d.into();
//         d.into()
//     }
// }

// /// **Warning**: wraps on underflow.
// impl Sub for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn sub(self, rhs: Ed25519FieldElement) -> Ed25519FieldElement {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         let a: BigUint = a.into();
//         let b: BigUint = b.into();
//         let max: BigUint = FieldCanvas::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").into();
//         let c: BigUint = if b > a { max.clone() - b + a } else { a - b };
//         let d: BigUint = c % max;
//         let d: FieldCanvas = d.into();
//         d.into()
//     }
// }

// /// **Warning**: wraps on overflow.
// impl Mul for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn mul(self, rhs: Ed25519FieldElement) -> Ed25519FieldElement {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         let a: BigUint = a.into();
//         let b: BigUint = b.into();
//         let c: BigUint = a * b;
//         let max: BigUint = FieldCanvas::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").into();
//         let d: BigUint = c % max;
//         let d: FieldCanvas = d.into();
//         d.into()
//     }
// }

// /// **Warning**: panics on division by 0.
// impl Div for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn div(self, rhs: Ed25519FieldElement) -> Ed25519FieldElement {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         let a: BigUint = a.into();
//         let b: BigUint = b.into();
//         let c: BigUint = a / b;
//         let max: BigUint = FieldCanvas::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").into();
//         let d: BigUint = c % max;
//         let d: FieldCanvas = d.into();
//         d.into()
//     }
// }

// /// **Warning**: panics on division by 0.
// impl Rem for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn rem(self, rhs: Ed25519FieldElement) -> Ed25519FieldElement {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         let a: BigUint = a.into();
//         let b: BigUint = b.into();
//         let c: BigUint = a % b;
//         let max: BigUint = FieldCanvas::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").into();
//         let d: BigUint = c % max;
//         let d: FieldCanvas = d.into();
//         d.into()
//     }
// }

// impl Not for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn not(self) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         (!a).into()
//     }
// }

// impl BitOr for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn bitor(self, rhs: Self) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         (a | b).into()
//     }
// }

// impl BitXor for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn bitxor(self, rhs: Self) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         (a ^ b).into()
//     }
// }

// impl BitAnd for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn bitand(self, rhs: Self) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         let b: FieldCanvas = rhs.into();
//         (a & b).into()
//     }
// }

// impl Shr<usize> for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn shr(self, rhs: usize) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         (a >> rhs).into()
//     }
// }

// impl Shl<usize> for Ed25519FieldElement {
//     type Output = Ed25519FieldElement;
//     fn shl(self, rhs: usize) -> Self::Output {
//         let a: FieldCanvas = self.into();
//         (a << rhs).into()
//     }
// }

// impl Ed25519FieldElement {
//     #[allow(dead_code)]
//     pub fn inv(self) -> Self {
//         let base: FieldCanvas = self.into();
//         base.inv(Self::max()).into()
//     }

//     #[allow(dead_code)]
//     pub fn pow_felem(self, exp: Self) -> Self {
//         let base: FieldCanvas = self.into();
//         base.pow_felem(exp.into(), Self::max()).into()
//     }
//     /// Returns self to the power of the argument.
//     /// The exponent is a u128.
//     #[allow(dead_code)]
//     pub fn pow(self, exp: u128) -> Self {
//         let base: FieldCanvas = self.into();
//         base.pow(exp, Self::max()).into()
//     }

//     /// Returns 2 to the power of the argument
//     #[allow(dead_code)]
//     pub fn pow2(x: usize) -> Ed25519FieldElement {
//         FieldCanvas::pow2(x).into()
//     }
// }


// // impl Ed25519FieldElement {
// //     pub fn from_byte_seq_be<A: SeqTrait<U8>>(s: &A) -> Ed25519FieldElement {
// //         FieldCanvas::from_be_bytes(s.iter().map(|x|
// //                                 U8::declassify(*x)).collect::<Vec<_>>().as_slice()).into()
// //     }
// //     pub fn from_public_byte_seq_be<A: SeqTrait<u8>>(s: A)
// //         -> Ed25519FieldElement {
// //         FieldCanvas::from_be_bytes(s.iter().map(|x|
// //                                 *x).collect::<Vec<_>>().as_slice()).into()
// //     }
// //     pub fn to_byte_seq_be(self) -> hacspec_lib::Seq<U8> {
// //         hacspec_lib::Seq::from_vec(self.to_be_bytes().iter().map(|x|
// //                         U8::classify(*x)).collect::<Vec<U8>>())
// //     }
// //     pub fn to_public_byte_seq_be(self) -> hacspec_lib::Seq<u8> {
// //         hacspec_lib::Seq::from_vec(self.to_be_bytes())
// //     }
// //     pub fn from_byte_seq_le<A: SeqTrait<U8>>(s: A) -> Ed25519FieldElement {
// //         FieldCanvas::from_le_bytes(s.iter().map(|x|
// //                                 U8::declassify(*x)).collect::<Vec<_>>().as_slice()).into()
// //     }
// //     pub fn from_public_byte_seq_le<A: SeqTrait<u8>>(s: A)
// //         -> Ed25519FieldElement {
// //         FieldCanvas::from_le_bytes(s.iter().map(|x|
// //                                 *x).collect::<Vec<_>>().as_slice()).into()
// //     }
// //     pub fn to_byte_seq_le(self) -> hacspec_lib::Seq<U8> {
// //         hacspec_lib::Seq::from_vec(self.to_le_bytes().iter().map(|x|
// //                         U8::classify(*x)).collect::<Vec<U8>>())
// //     }
// //     pub fn to_public_byte_seq_le(self) -> hacspec_lib::Seq<u8> {
// //         hacspec_lib::Seq::from_vec(self.to_le_bytes())
// //     }
// //     pub fn from_secret_literal(x: U128) -> Ed25519FieldElement {
// //         FieldCanvas::from_literal(U128::declassify(x)).into()
// //     }
// // }

// // impl NumericCopy for Ed25519FieldElement {}
// // impl UnsignedInteger for Ed25519FieldElement {}
// // impl UnsignedIntegerCopy for Ed25519FieldElement {}

// // impl Integer for Ed25519FieldElement {
// //     const NUM_BITS: usize = 256;
// //     #[inline]
// //     fn ZERO() -> Self { Self::from_literal(0) }
// //     #[inline]
// //     fn ONE() -> Self { Self::from_literal(1) }
// //     #[inline]
// //     fn TWO() -> Self { Self::from_literal(2) }
// //     #[inline]
// //     fn from_literal(val: u128) -> Self { Self::from_literal(val) }
// //     #[inline]
// //     fn from_hex_string(s: &String) -> Self {
// //         Self::from_hex(&s.replace("0x", ""))
// //     }
// //     /// Get bit `i` of this integer.
// //     #[inline]
// //     fn get_bit(self, i: usize) -> Self { (self >> i) & Self::ONE() }
// //     /// Set bit `i` of this integer to `b` and return the result.
// //     /// Bit `b` has to be `0` or `1`.
// //     #[inline]
// //     fn set_bit(self, b: Self, i: usize) -> Self {
// //         if true {
// //                 if !(b.clone().equal(Self::ONE()) ||
// //                                 b.clone().equal(Self::ZERO())) {
// //                         ::core::panicking::panic("assertion failed: b.clone().equal(Self::ONE()) || b.clone().equal(Self::ZERO())")
// //                     };
// //             };
// //         let tmp1 = Self::from_literal(!(1 << i));
// //         let tmp2 = b << i;
// //         (self & tmp1) | tmp2
// //     }
// //     /// Set bit `pos` of this integer to bit `yi` of integer `y`.
// //     #[inline]
// //     fn set(self, pos: usize, y: Self, yi: usize) -> Self {
// //         let b = y.get_bit(yi);
// //         self.set_bit(b, pos)
// //     }
// //     fn rotate_left(self, n: usize) -> Self {
// //         if !(n < Self::NUM_BITS) {
// //                 ::core::panicking::panic("assertion failed: n < Self::NUM_BITS")
// //             };
// //         (self.clone() << n) |
// //             (self >> ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
// //     }
// //     fn rotate_right(self, n: usize) -> Self {
// //         if !(n < Self::NUM_BITS) {
// //                 ::core::panicking::panic("assertion failed: n < Self::NUM_BITS")
// //             };
// //         (self.clone() >> n) |
// //             (self << ((-(n as i32) as usize) & (Self::NUM_BITS - 1)))
// //     }
// // }

// // impl ModNumeric for Ed25519FieldElement {
// //     /// (self - rhs) % n.
// //     fn sub_mod(self, rhs: Self, n: Self) -> Self { self - rhs }
// //     /// `(self + rhs) % n`
// //     fn add_mod(self, rhs: Self, n: Self) -> Self { self + rhs }
// //     /// `(self * rhs) % n`
// //     fn mul_mod(self, rhs: Self, n: Self) -> Self { self * rhs }
// //     /// `(self ^ exp) % n`
// //     fn pow_mod(self, exp: Self, n: Self) -> Self { self.pow_felem(exp) }
// //     /// `self % n`
// //     fn modulo(self, n: Self) -> Self { self % n }
// //     /// `self % n` that always returns a positive integer
// //     fn signed_modulo(self, n: Self) -> Self { self.modulo(n) }
// //     /// `|self|`
// //     fn absolute(self) -> Self { self }
// // }

// // impl Numeric for Ed25519FieldElement {
// //     /// Return largest value that can be represented.
// //     fn max_val() -> Self {
// //         (Self::max() - FieldCanvas::from_literal(1)).into()
// //     }
// //     fn wrap_add(self, rhs: Self) -> Self { self + rhs }
// //     fn wrap_sub(self, rhs: Self) -> Self { self - rhs }
// //     fn wrap_mul(self, rhs: Self) -> Self { self * rhs }
// //     fn wrap_div(self, rhs: Self) -> Self { self / rhs }
// //     /// `self ^ exp` where `exp` is a `u32`.
// //     fn exp(self, exp: u32) -> Self { self.pow(exp.into()) }
// //     /// `self ^ exp` where `exp` is a `Self`.
// //     fn pow_self(self, exp: Self) -> Self { self.pow_felem(exp) }
// //     /// Division.
// //     fn divide(self, rhs: Self) -> Self { self / rhs }
// //     /// Invert self modulo n.
// //     /// **NOTE:** `n` is ignored and inversion is done with respect to
// //     ///            the modulus.
// //     fn inv(self, n: Self) -> Self { self.inv() }
// //     fn equal(self, other: Self) -> bool { self == other }
// //     fn greater_than(self, other: Self) -> bool { self > other }
// //     fn greater_than_or_qual(self, other: Self) -> bool { self >= other }
// //     fn less_than(self, other: Self) -> bool { self < other }
// //     fn less_than_or_equal(self, other: Self) -> bool { self <= other }
// //     fn not_equal_bm(self, other: Self) -> Self {
// //         if self != other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// //     fn equal_bm(self, other: Self) -> Self {
// //         if self == other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// //     fn greater_than_bm(self, other: Self) -> Self {
// //         if self > other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// //     fn greater_than_or_equal_bm(self, other: Self) -> Self {
// //         if self >= other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// //     fn less_than_bm(self, other: Self) -> Self {
// //         if self < other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// //     fn less_than_or_equal_bm(self, other: Self) -> Self {
// //         if self <= other {
// //                 (Self::ONE() << (256 - 1)) - Self::ONE()
// //             } else { Self::ZERO() }
// //     }
// // }

// #[ensures(result == 42u32)]
// fn the_answer() -> u32 { return 42u32; }
// fn cmov(a: Ed25519FieldElement, b: Ed25519FieldElement, c: bool)
//     -> Ed25519FieldElement {
//     if c { b } else { a }
// }
