//!
//! # Arrays
//!
//! This module implements fixed-length arrays and utility functions for it.
//!
//! Note that implementations have to be created with one of the provided macros
//! such that there's no documentation in here.
//!
//! You can find examples for the different types of arrays here:
//! * [DocSecretBytes](../struct.DocSecretBytes.html) for `bytes!(DocSecretBytes, 64)`
//! * [DocPublicBytes](../struct.DocPublicBytes.html) for `public_bytes!(DocPublicBytes, 64)`
//! * [DocSecretArray](../struct.DocSecretArray.html) for `array!(DocSecretArray, 64, U32)`
//! * [DocPublicArray](../struct.DocPublicArray.html) for `array!(DocPublicArray, 64, u32)`
//!
//! **Note** that all macros starting with an underscore (`_array_base` etc.)
//! are note intended for public use. Unfortunately it's not possible to hide
//! them.

#[macro_export]
macro_rules! _array_base {
    ($name:ident,$l:expr,$t:ty) => {
        /// Fixed length byte array.
        // Because Rust requires fixed length arrays to have a known size at
        // compile time there's no generic fixed length byte array here.
        // Use this to define the fixed length byte arrays needed in your code.
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        pub struct $name(pub [$t; $l]);

        impl $name {
            pub fn len(&self) -> usize {
                $l
            }

            #[primitive(hacspec)]
            pub fn from_array(v: [$t; $l]) -> Self {
                Self(v.clone())
            }

            pub fn from_slice(v: &[$t]) -> Self {
                debug_assert!(v.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for i in 0..v.len() {
                    tmp[i] = v[i];
                }
                Self(tmp.clone())
            }
        }

        impl $name {
            #[primitive(hacspec)]
            pub fn new() -> Self {
                Self([<$t>::default(); $l])
            }

            #[external(hacspec)]
            pub fn capacity() -> usize {
                $l
            }

            #[library(hacspec)]
            pub fn from_sub<A: SeqTrait<$t>>(input: A, start: usize, len: usize) -> Self {
                let mut a = Self::new();
                debug_assert_eq!(len, a.len());
                a = a.update_sub(0, input, start, len);
                a
            }

            #[library(hacspec)]
            pub fn from_subr<A: SeqTrait<$t>>(input: A, r: Range<usize>) -> Self {
                Self::from_sub(input, r.start, r.end - r.start)
            }

            #[library(hacspec)]
            pub fn sub(self, start_out: usize, len: usize) -> Seq<$t> {
                Seq::from_sub(self, start_out, len)
            }

            #[library(hacspec)]
            pub fn subr(self, r: Range<usize>) -> Seq<$t> {
                self.sub(r.start, r.end - r.start)
            }

            #[library(hacspec)]
            pub fn num_chunks(
                &self,
                chunk_size: usize
            ) -> usize {
                (self.len() + chunk_size - 1) / chunk_size
            }

            #[library(hacspec)]
            pub fn get_chunk(
                self,
                chunk_size: usize,
                chunk_number: usize
            ) -> (usize, Seq<$t>) {
                let idx_start = chunk_size * chunk_number;
                let len = if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                };
                let out = self.sub(idx_start, len);
                (len, out)
            }

            #[library(hacspec)]
            pub fn set_chunk<A: SeqTrait<$t>>(
                self,
                chunk_size: usize,
                chunk_number: usize,
                input: A,
            ) -> Self {
                let idx_start = chunk_size * chunk_number;
                let len = if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                };
                debug_assert!(input.len() == len, "the chunk length should match the input");
                self.update_sub(idx_start, input, 0, len)
            }
        }

        impl Default for $name {
            #[library(hacspec)]
            fn default() -> Self {
                $name::new()
            }
        }
        impl AsMut<[$t]> for $name {
            #[to_remove(hacspec)]
            fn as_mut(&mut self) -> &mut [$t] {
                &mut self.0
            }
        }
        impl SeqTrait<$t> for $name {
            #[primitive(hacspec)]
            fn len(&self) -> usize {
                $l
            }
            #[external(hacspec)]
            fn iter(&self) -> std::slice::Iter<$t> {
                self.0.iter()
            }
        }

        impl Index<usize> for $name {
            type Output = $t;
            #[primitive(hacspec)]
            fn index(&self, i: usize) -> &$t {
                &self.0[i]
            }
        }
        impl IndexMut<usize> for $name {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: usize) -> &mut $t {
                &mut self.0[i]
            }
        }

        impl Index<u8> for $name {
            type Output = $t;
            #[primitive(hacspec)]
            fn index(&self, i: u8) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u8> for $name {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: u8) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<u32> for $name {
            type Output = $t;
            #[primitive(hacspec)]
            fn index(&self, i: u32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u32> for $name {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: u32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<i32> for $name {
            type Output = $t;
            #[primitive(hacspec)]
            fn index(&self, i: i32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<i32> for $name {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: i32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<RangeFull> for $name {
            type Output = [$t];
            #[primitive(hacspec)]
            fn index(&self, r: RangeFull) -> &[$t] {
                &self.0[r]
            }
        }
        impl $name {
            #[external(hacspec)]
            pub fn from_vec(x: Vec<$t>) -> $name {
                debug_assert_eq!(x.len(), $l);
                let mut tmp = [<$t>::default(); $l];
                for (i, e) in x.iter().enumerate() {
                    tmp[i] = *e;
                }
                $name(tmp.clone())
            }

            // We can't use the [From] trait here because otherwise it would conflict with
            // the From<T> for T core implementation, as the array also implements the [SeqTrait].
            #[library(hacspec)]
            pub fn from_seq<T: SeqTrait<$t>>(x: T) -> $name {
                debug_assert_eq!(x.len(), $l);
                let mut out = $name::new();
                for i in 0..x.len() {
                    out[i] = x[i];
                }
                out
            }
        }

        impl $name {
            #[external(hacspec)]
            pub fn random() -> $name {
                let mut tmp = [<$t>::default(); $l];
                tmp.copy_from_slice(&$name::get_random_vec($l)[..$l]);
                Self(tmp.clone())
            }
            fn hex_string_to_vec(s: &str) -> Vec<$t> {
                debug_assert!(s.len() % std::mem::size_of::<$t>() == 0);
                let b: Result<Vec<$t>, ParseIntError> = (0..s.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map(<$t>::from))
                    .collect();
                b.expect("Error parsing hex string")
            }

            /// Read hex string to Bytes.
            #[primitive(hacspec)]
            pub fn from_hex(s: &str) -> $name {
                let v = $name::hex_string_to_vec(s);
                let mut o = $name::new();
                debug_assert!(v.len() == $l);
                for i in 0..$l {
                    o[i] = v[i]
                }
                o
            }
        }

        // /// Element wise xor of two arrays
        // impl std::ops::BitXor for $name {
        //     type Output = Self;
        //     fn bitxor(self, rhs: Self) -> Self::Output {
        //         let mut out = Self::new();
        //         for (a, (b, c)) in out.0.iter_mut().zip(self.0.iter().zip(rhs.0.iter())) {
        //             *a = *b ^ *c;
        //         }
        //         out
        //     }
        // }
    };
}

#[macro_export]
/// This creates arrays for secret integers, i.e. `$t` is the secret integer
/// type and `$tbase` is the according Rust type.
macro_rules! _secret_array {
    ($name:ident,$l:expr,$t:ty, $tbase:ty) => {
        _array_base!($name, $l, $t);

        /// **Warning:** declassifies secret integer types.
        impl fmt::Debug for $name {
            #[external(hacspec)]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..]
                    .iter()
                    .map(|x| <$t>::declassify(*x))
                    .collect::<Vec<_>>()
                    .fmt(f)
            }
        }
        /// **Warning:** declassifies secret integer types.
        impl PartialEq for $name {
            #[to_remove(hacspec)]
            fn eq(&self, other: &Self) -> bool {
                self.0[..]
                    .iter()
                    .map(|x| <$t>::declassify(*x))
                    .collect::<Vec<_>>()
                    == other.0[..]
                        .iter()
                        .map(|x| <$t>::declassify(*x))
                        .collect::<Vec<_>>()
            }
        }
        impl $name {
            #[external(hacspec)]
            pub fn get_random_vec(l: usize) -> Vec<$t> {
                (0..l)
                    .map(|_| <$t>::classify(rand::random::<$tbase>()))
                    .collect()
            }

            #[primitive(hacspec)]
            pub fn to_bytes_be(self) -> Seq<U8> {
               const FACTOR: usize = core::mem::size_of::<$t>();
               let mut out : Seq<U8> = Seq::new($l * FACTOR);
               for i in 0..$l {
                   let tmp : $t = self[i];
                   let tmp = <$t>::to_bytes_be(&[tmp]);
                   for j in 0..FACTOR {
                       out[i * FACTOR + j] = tmp[j];
                   }
               }
               out
            }
        }
        impl $name {
            #[external(hacspec)]
            pub fn from_public_slice(v: &[$tbase]) -> $name {
                debug_assert!(v.len() == $l);
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }

            /// Create an array from a regular Rust array.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// bytes!(Block, 5);
            /// let b = Block::from_public_array([1, 2, 3, 4, 5]);
            /// ```
            #[external(hacspec)]
            pub fn from_public_array(v: [$tbase; $l]) -> $name {
                debug_assert!(v.len() == $l);
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }
        }
    };
}

#[macro_export]
macro_rules! _public_array {
    ($name:ident,$l:expr,$t:ty) => {
        _array_base!($name, $l, $t);
        impl $name {
            #[external(hacspec)]
            pub fn get_random_vec(l: usize) -> Vec<$t> {
                (0..l).map(|_| rand::random::<$t>()).collect()
            }
        }

        impl fmt::Debug for $name {
            #[external(hacspec)]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..].fmt(f)
            }
        }
        impl PartialEq for $name {
            #[primitive(hacspec)]
            fn eq(&self, other: &Self) -> bool {
                self.0[..] == other.0[..]
            }
        }
    };
}

// The following are the macros intended for use from the outside.

#[macro_export]
/// Create a new array with the given name, length, and type.
macro_rules! array {
    ($name:ident, $l:expr, U8) => {
        _secret_array!($name, $l, U8, u8);
        _implement_numeric_unsigned_secret!($name);

        impl $name {
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U32s_be(&self) -> Seq<U32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = U32_from_be_bytes(U32Word::from_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U32s_le(&self) -> Seq<U32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = U32_from_le_bytes(U32Word::from_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U64s_be(&self) -> Seq<U64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = U64_from_be_bytes(U64Word::from_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U64s_le(&self) -> Seq<U64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = U64_from_le_bytes(U64Word::from_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U128s_be(&self) -> Seq<U128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = U128_from_be_bytes(U128Word::from_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[primitive(hacspec)]
            pub fn to_U128s_le(&self) -> Seq<U128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = U128_from_le_bytes(U128Word::from_slice(block));
                }
                out
            }
            #[external(hacspec)]
            pub fn to_hex(&self) -> String {
                let strs: Vec<String> = self.0.iter().map(|b| format!("{:02x}", b)).collect();
                strs.join("")
            }
        }
    };
    ($name:ident, $l:expr, U16) => {
        _secret_array!($name, $l, U16, u16);
        _implement_numeric_unsigned_secret!($name);
    };
    ($name:ident, $l:expr, U32) => {
        _secret_array!($name, $l, U32, u32);
        _implement_numeric_unsigned_secret!($name);
    };
    ($name:ident, $l:expr, U64) => {
        _secret_array!($name, $l, U64, u64);
        _implement_numeric_unsigned_secret!($name);
    };
    ($name:ident, $l:expr, U128) => {
        _secret_array!($name, $l, U128, u128);
        _implement_numeric_unsigned_secret!($name);
    };
    ($name:ident, $l:expr, u8) => {
        _public_array!($name, $l, u8);
        _implement_numeric_unsigned_public!($name);

        impl $name {
            #[primitive(hacspec)]
            pub fn to_u32s_be(&self) -> Seq<u32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = u32::from_be_bytes(to_array(block));
                }
                out
            }
            #[primitive(hacspec)]
            pub fn to_u32s_le(&self) -> Seq<u32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = u32::from_le_bytes(to_array(block));
                }
                out
            }
            #[primitive(hacspec)]
            pub fn to_u64s_be(&self) -> Seq<u64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = u64::from_be_bytes(to_array(block));
                }
                out
            }
            #[primitive(hacspec)]
            pub fn to_u64s_le(&self) -> Seq<u64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = u64::from_le_bytes(to_array(block));
                }
                out
            }
            #[primitive(hacspec)]
            pub fn to_u128s_be(&self) -> Seq<u128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = u128::from_be_bytes(to_array(block));
                }
                out
            }
            #[primitive(hacspec)]
            pub fn to_u128s_le(&self) -> Seq<u128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = u128::from_le_bytes(to_array(block));
                }
                out
            }
            #[external(hacspec)]
            pub fn to_hex(&self) -> String {
                let strs: Vec<String> = self.0.iter().map(|b| format!("{:02x}", b)).collect();
                strs.join("")
            }
        }
    };
    ($name:ident, $l:expr, u16) => {
        _public_array!($name, $l, u16);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u32) => {
        _public_array!($name, $l, u32);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u64) => {
        _public_array!($name, $l, u64);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u128) => {
        _public_array!($name, $l, u128);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, $t:ty) => {
        _public_array!($name, $l, $t);
    };
}

#[macro_export]
/// Convenience function to create a new byte array (of type `U8`) with the given
/// name and length.
macro_rules! bytes {
    ($name:ident, $l:expr) => {
        array!($name, $l, U8);
    };
}

#[macro_export]
/// Convenience function to create a new public byte array (of type `u8`) with
/// the given name and length.
macro_rules! public_bytes {
    ($name:ident, $l:expr) => {
        array!($name, $l, u8);
    };
}

#[macro_export]
macro_rules! both_arrays {
    ($public_name:ident, $name:ident, $l:expr, $t:ty, $tbase:ty) => {
        _secret_array!($name, $l, $t, $tbase);
        _public_array!($public_name, $l, $tbase);

        impl $name {
            /// Conversion function between public and secret array versions.
            #[primitive(hacspec)]
            pub fn from_public(v: $public_name) -> $name {
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }
        }

        impl $public_name {
            /// *Warning:* this function declassifies secret integers!
            #[primitive(hacspec)]
            pub fn from_secret_declassify(v: $name) -> $public_name {
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$t>::declassify(*x))
                        .collect::<Vec<$tbase>>(),
                )
            }
        }
    };
}

#[macro_export]
macro_rules! both_bytes {
    ($public_name:ident, $name:ident, $l:expr) => {
        both_arrays!($public_name, $name, $l, U8, u8);
    };
}
