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
        /// Because Rust requires fixed length arrays to have a known size at
        /// compile time there's no generic fixed length byte array here.
        /// Use this to define the fixed length byte arrays needed in your code.
        #[derive(Clone, Copy)]
        pub struct $name(pub [$t; $l]);

        impl From<[$t; $l]> for $name {
            fn from(v: [$t; $l]) -> Self {
                Self(v.clone())
            }
        }

        impl From<&[$t]> for $name {
            fn from(v: &[$t]) -> Self {
                debug_assert!(v.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for i in 0..v.len() {
                    tmp[i] = v[i];
                }
                Self(tmp.clone())
            }
        }

        impl $name {
            pub fn new() -> Self {
                Self([<$t>::default(); $l])
            }
            pub fn capacity() -> usize {
                $l
            }

            pub fn from_sub_pad<A: SeqTrait<$t>>(input: A, r: Range<usize>) -> Self {
                let mut a = Self::default();
                for (i, v) in r
                    .clone()
                    .zip(input.iter().skip(r.start).take(r.end - r.start))
                {
                    a[i - r.start] = *v;
                }
                a
            }

            pub fn from_sub<A: SeqTrait<$t>>(input: A, r: Range<usize>) -> Self {
                debug_assert!(
                    $l == r.end - r.start,
                    "sub range is not the length of the output type "
                );
                $name::from_sub_pad(input, r)
            }

            pub fn copy_pad<A: SeqTrait<$t>>(v: A) -> Self {
                debug_assert!(v.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for (i, x) in v.iter().enumerate() {
                    tmp[i] = *x;
                }
                Self(tmp.clone())
            }
            pub fn copy<A: SeqTrait<$t>>(v: A) -> Self {
                debug_assert!(v.len() == $l);
                let mut tmp = [<$t>::default(); $l];
                for (i, x) in v.iter().enumerate() {
                    tmp[i] = *x;
                }
                Self(tmp.clone())
            }
            pub fn update<A: SeqTrait<$t>>(mut self, start: usize, v: A) -> Self {
                debug_assert!(self.len() >= start + v.len());
                for (i, b) in v.iter().enumerate() {
                    self[start + i] = *b;
                }
                self
            }
            pub fn update_sub<A: SeqTrait<$t>>(
                mut self,
                start_out: usize,
                v: A,
                start_in: usize,
                len: usize,
            ) -> Self {
                debug_assert!(self.len() >= start_out + len);
                debug_assert!(v.len() >= start_in + len);
                for (i, b) in v.iter().skip(start_in).take(len).enumerate() {
                    self[start_out + i] = *b;
                }
                self
            }
            pub fn len(&self) -> usize {
                $l
            }
            pub fn to_bytes_be(&self) -> [u8; $l * core::mem::size_of::<$t>()] {
                const FACTOR: usize = core::mem::size_of::<$t>();
                let mut out = [0u8; $l * FACTOR];
                for i in 0..$l {
                    let tmp = <$t>::from(self[i]).to_be_bytes();
                    for j in 0..FACTOR {
                        out[i * FACTOR + j] = tmp[j];
                    }
                }
                out
            }

            /// Get an iterator over this array with chunks of size `chunk_size`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// public_bytes!(Block, 5);
            /// let a = Block::from([0, 1, 2, 3, 4]);
            /// let mut a_chunks = a.chunks(2);
            /// let a_chunk = a_chunks.next().unwrap();
            /// // assert_eq!(a_chunk.0, 2);
            /// // assert_eq!(a_chunk.1, Seq::<u8>::from_array(&[0, 1]));
            /// let a_chunk = a_chunks.next().unwrap();
            /// // assert_eq!(a_chunk.0, 2);
            /// // assert_eq!(a_chunk.1, Seq::<u8>::from_array(&[2, 3]));
            /// let a_chunk = a_chunks.next().unwrap();
            /// // assert_eq!(a_chunk.0, 1);
            /// // assert_eq!(a_chunk.1, Seq::<u8>::from_array(&[4]));
            ///
            /// let a = Block::from([0, 1, 2, 3, 4]);
            /// for (l, chunk) in a.chunks(2) {
            ///     println!("{:x?}", chunk); // prints [0, 1], [2, 3], [4]
            /// }
            /// ```
            pub fn chunks<'a>(
                &'a self,
                chunk_size: usize,
            ) -> impl Iterator<Item = (usize, Seq<$t>)> + 'a {
                self.0
                    .chunks(chunk_size)
                    .map(|c| (c.len(), Seq::<$t>::from(c)))
            }

            fn iter_mut(&mut self) -> std::slice::IterMut<$t> {
                self.0.iter_mut()
            }
        }

        impl Default for $name {
            fn default() -> Self {
                $name::new()
            }
        }
        impl AsMut<[$t]> for $name {
            fn as_mut(&mut self) -> &mut [$t] {
                &mut self.0
            }
        }
        impl SeqTrait<$t> for $name {
            fn raw<'a>(&'a self) -> &'a [$t] {
                &self.0
            }
            fn len(&self) -> usize {
                $l
            }
            fn iter(&self) -> std::slice::Iter<$t> {
                self.0.iter()
            }
        }

        impl Index<usize> for $name {
            type Output = $t;
            fn index(&self, i: usize) -> &$t {
                &self.0[i]
            }
        }
        impl IndexMut<usize> for $name {
            fn index_mut(&mut self, i: usize) -> &mut $t {
                &mut self.0[i]
            }
        }

        impl Index<u8> for $name {
            type Output = $t;
            fn index(&self, i: u8) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u8> for $name {
            fn index_mut(&mut self, i: u8) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<u32> for $name {
            type Output = $t;
            fn index(&self, i: u32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u32> for $name {
            fn index_mut(&mut self, i: u32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<i32> for $name {
            type Output = $t;
            fn index(&self, i: i32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<i32> for $name {
            fn index_mut(&mut self, i: i32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<RangeFull> for $name {
            type Output = [$t];
            fn index(&self, r: RangeFull) -> &[$t] {
                &self.0[r]
            }
        }
        impl From<Vec<$t>> for $name {
            fn from(x: Vec<$t>) -> $name {
                debug_assert!(x.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for (i, e) in x.iter().enumerate() {
                    tmp[i] = *e;
                }
                $name(tmp.clone())
            }
        }
        impl From<Seq<$t>> for $name {
            fn from(x: Seq<$t>) -> $name {
                debug_assert!(x.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for (i, e) in x.iter().enumerate() {
                    tmp[i] = *e;
                }
                $name(tmp.clone())
            }
        }

        impl $name {
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
        }

        /// Read hex string to Bytes.
        impl From<&str> for $name {
            fn from(s: &str) -> $name {
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
            pub fn get_random_vec(l: usize) -> Vec<$t> {
                (0..l)
                    .map(|_| <$t>::classify(rand::random::<$tbase>()))
                    .collect()
            }
        }
        impl From<&[$tbase]> for $name {
            fn from(v: &[$tbase]) -> $name {
                debug_assert!(v.len() <= $l);
                Self::from(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }
        }
        /// Create an array from a regular Rust array.
        ///
        /// # Examples
        ///
        /// ```
        /// use hacspec::prelude::*;
        ///
        /// bytes!(Block, 5);
        /// let b = Block::from([1, 2, 3, 4, 5]);
        /// ```
        impl From<[$tbase; $l]> for $name {
            fn from(v: [$tbase; $l]) -> $name {
                debug_assert!(v.len() == $l);
                Self::from(
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
            pub fn get_random_vec(l: usize) -> Vec<$t> {
                (0..l).map(|_| rand::random::<$t>()).collect()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..].fmt(f)
            }
        }
        impl PartialEq for $name {
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
            pub fn to_U32s_be(&self) -> [U32; $l / 4] {
                let mut out = [U32::default(); $l / 4];
                for (i, block) in self.0.chunks(4).enumerate() {
                    out[i] = u32_from_be_bytes(block.into());
                }
                out
            }
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
            pub fn to_u32s_be(&self) -> [u32; $l / 4] {
                let mut out = [0u32; $l / 4];
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = u32::from_be_bytes(to_array(block));
                }
                out
            }
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

        // Conversion function between public and secret array versions.
        impl From<$public_name> for $name {
            fn from(v: $public_name) -> $name {
                Self::from(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }
        }
        impl From<$name> for $public_name {
            fn from(v: $name) -> $public_name {
                Self::from(
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
