//!
//! # Arrays
//!
//! This module implements fixed-length arrays and utility functions for it.
//!
//! **Note** that all macros starting with an underscore (`_array_base` etc.)
//! are note intended for public use. Unfortunately it's not possible to hide
//! them.
//!
//! To define a new array type with name `State`, holding `16` `u32` run
//!
//! ```
//! use hacspec_lib::prelude::*;
//! array!(State, 16, u32, type_for_indexes: StateIdx);
//! ```
//!
//! ## Instantiating Arrays
//! There are several different ways of creating array types.
//!
//! ###

#[macro_export]
#[doc(hidden)]
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
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn new() -> Self {
                Self([<$t>::default(); $l])
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn length() -> usize {
                $l
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn from_array(v: [$t; $l]) -> Self {
                Self(v.clone())
            }

            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn from_native_slice(v: &[$t]) -> Self {
                debug_assert!(v.len() <= $l);
                let mut tmp = [<$t>::default(); $l];
                for i in 0..v.len() {
                    tmp[i] = v[i];
                }
                Self(tmp.clone())
            }
        }

        impl $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_slice<A: SeqTrait<$t>>(input: &A, start: usize, len: usize) -> Self {
                let mut a = Self::new();
                debug_assert!(len <= a.len(), "{} > {}", len, a.len());
                a = a.update_slice(0, input, start, len);
                a
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn concat<A: SeqTrait<$t>>(&self, next: &A) -> Seq<$t> {
                let mut out = Seq::new(self.len() + next.len());
                out = out.update_start(self);
                out = out.update_slice(self.len(), next, 0, next.len());
                out
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_slice_range<A: SeqTrait<$t>>(input: &A, r: Range<usize>) -> Self {
                Self::from_slice(input, r.start, r.end - r.start)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn slice(&self, start_out: usize, len: usize) -> Seq<$t> {
                Seq::from_slice(self, start_out, len)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn slice_range(&self, r: Range<usize>) -> Seq<$t> {
                self.slice(r.start, r.end - r.start)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn num_chunks(&self, chunk_size: usize) -> usize {
                (self.len() + chunk_size - 1) / chunk_size
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn get_chunk_len(&self, chunk_size: usize, chunk_number: usize) -> usize {
                let idx_start = chunk_size * chunk_number;
                if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                }
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn get_chunk(&self, chunk_size: usize, chunk_number: usize) -> (usize, Seq<$t>) {
                let idx_start = chunk_size * chunk_number;
                let len = self.get_chunk_len(chunk_size, chunk_number);
                let out = self.slice(idx_start, len);
                (len, out)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn set_chunk<A: SeqTrait<$t>>(
                self,
                chunk_size: usize,
                chunk_number: usize,
                input: &A,
            ) -> Self {
                let idx_start = chunk_size * chunk_number;
                let len = self.get_chunk_len(chunk_size, chunk_number);
                debug_assert!(
                    input.len() == len,
                    "the chunk length should match the input. got {}, expected {}",
                    input.len(),
                    len
                );
                self.update_slice(idx_start, input, 0, len)
            }
        }

        impl Default for $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn default() -> Self {
                $name::new()
            }
        }
        impl SeqTrait<$t> for $name {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn create(x: usize) -> Self {
                assert_eq!(x, $l);
                Self::new()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn len(&self) -> usize {
                $l
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn iter(&self) -> core::slice::Iter<$t> {
                self.0.iter()
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update_slice<A: SeqTrait<$t>>(
                mut self,
                start_out: usize,
                v: &A,
                start_in: usize,
                len: usize,
            ) -> Self {
                debug_assert!(self.len() >= start_out + len);
                debug_assert!(v.len() >= start_in + len);
                for i in 0..len {
                    self[start_out + i] = v[start_in + i];
                }
                self
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update<A: SeqTrait<$t>>(self, start: usize, v: &A) -> Self {
                let len = v.len();
                self.update_slice(start, v, 0, len)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update_start<A: SeqTrait<$t>>(self, v: &A) -> Self {
                let len = v.len();
                self.update_slice(0, v, 0, len)
            }
        }

        impl Index<usize> for $name {
            type Output = $t;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: usize) -> &$t {
                &self.0[i]
            }
        }
        impl IndexMut<usize> for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index_mut(&mut self, i: usize) -> &mut $t {
                &mut self.0[i]
            }
        }

        impl Index<u8> for $name {
            type Output = $t;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: u8) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u8> for $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: u8) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<u32> for $name {
            type Output = $t;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: u32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<u32> for $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: u32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<i32> for $name {
            type Output = $t;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: i32) -> &$t {
                &self.0[i as usize]
            }
        }
        impl IndexMut<i32> for $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: i32) -> &mut $t {
                &mut self.0[i as usize]
            }
        }
        impl Index<RangeFull> for $name {
            type Output = [$t];
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, r: RangeFull) -> &[$t] {
                &self.0[r]
            }
        }
        impl $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
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
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_seq<T: SeqTrait<$t>>(x: &T) -> $name {
                debug_assert_eq!(x.len(), $l);
                let mut out = $name::new();
                for i in 0..x.len() {
                    out[i] = x[i];
                }
                out
            }
        }

        impl $name {
            fn hex_string_to_vec(s: &str) -> Vec<$t> {
                debug_assert!(s.len() % core::mem::size_of::<$t>() == 0);
                let b: Result<Vec<$t>, ParseIntError> = (0..s.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map(<$t>::from))
                    .collect();
                b.expect("Error parsing hex string")
            }

            /// Read hex string to Bytes.
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
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
    };
}

#[macro_export]
macro_rules! generic_array {
    ($name:ident,$l:expr) => {
        /// Fixed length byte array.
        // Because Rust requires fixed length arrays to have a known size at
        // compile time there's no generic fixed length byte array here.
        // Use this to define the fixed length byte arrays needed in your code.
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy)]
        pub struct $name<T>(pub [T; $l]);

        impl<T: Numeric + Copy> $name<T> {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn new() -> Self {
                Self([<T>::default(); $l])
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn length() -> usize {
                $l
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn from_array(v: [T; $l]) -> Self {
                Self(v.clone())
            }

            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn from_native_slice(v: &[T]) -> Self {
                debug_assert!(v.len() <= $l);
                let mut tmp = [<T>::default(); $l];
                for i in 0..v.len() {
                    tmp[i] = v[i];
                }
                Self(tmp.clone())
            }
        }

        impl<T: Numeric + Copy> $name<T> {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_slice<A: SeqTrait<T>>(input: &A, start: usize, len: usize) -> Self {
                let mut a = Self::new();
                debug_assert!(len <= a.len());
                a = a.update_slice(0, input, start, len);
                a
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn concat<A: SeqTrait<T>>(&self, next: &A) -> Seq<T> {
                let mut out = Seq::new(self.len() + next.len());
                out = out.update_start(self);
                out = out.update_slice(self.len(), next, 0, next.len());
                out
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_slice_range<A: SeqTrait<T>>(input: &A, r: Range<usize>) -> Self {
                Self::from_slice(input, r.start, r.end - r.start)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn slice(&self, start_out: usize, len: usize) -> Seq<T> {
                Seq::from_slice(self, start_out, len)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn slice_range(&self, r: Range<usize>) -> Seq<T> {
                self.slice(r.start, r.end - r.start)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn num_chunks(&self, chunk_size: usize) -> usize {
                (self.len() + chunk_size - 1) / chunk_size
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn get_chunk_len(&self, chunk_size: usize, chunk_number: usize) -> usize {
                let idx_start = chunk_size * chunk_number;
                if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                }
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn get_chunk(&self, chunk_size: usize, chunk_number: usize) -> (usize, Seq<T>) {
                let idx_start = chunk_size * chunk_number;
                let len = self.get_chunk_len(chunk_size, chunk_number);
                let out = self.slice(idx_start, len);
                (len, out)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn set_chunk<A: SeqTrait<T>>(
                self,
                chunk_size: usize,
                chunk_number: usize,
                input: &A,
            ) -> Self {
                let idx_start = chunk_size * chunk_number;
                let len = self.get_chunk_len(chunk_size, chunk_number);
                debug_assert!(
                    input.len() == len,
                    "the chunk length should match the input. got {}, expected {}",
                    input.len(),
                    len
                );
                self.update_slice(idx_start, input, 0, len)
            }
        }

        impl<T: Numeric + Copy> Default for $name<T> {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn default() -> Self {
                $name::new()
            }
        }
        impl<T: Numeric + Copy> SeqTrait<T> for $name<T> {
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn create(x: usize) -> Self {
                assert_eq!(x, $l);
                Self::new()
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn len(&self) -> usize {
                $l
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn iter(&self) -> core::slice::Iter<T> {
                self.0.iter()
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update_slice<A: SeqTrait<T>>(
                mut self,
                start_out: usize,
                v: &A,
                start_in: usize,
                len: usize,
            ) -> Self {
                debug_assert!(self.len() >= start_out + len);
                debug_assert!(v.len() >= start_in + len);
                for i in 0..len {
                    self[start_out + i] = v[start_in + i];
                }
                self
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update<A: SeqTrait<T>>(self, start: usize, v: &A) -> Self {
                let len = v.len();
                self.update_slice(start, v, 0, len)
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update_start<A: SeqTrait<T>>(self, v: &A) -> Self {
                let len = v.len();
                self.update_slice(0, v, 0, len)
            }
        }

        impl<T: Numeric + Copy> Index<usize> for $name<T> {
            type Output = T;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: usize) -> &T {
                &self.0[i]
            }
        }
        impl<T: Numeric + Copy> IndexMut<usize> for $name<T> {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index_mut(&mut self, i: usize) -> &mut T {
                &mut self.0[i]
            }
        }

        impl<T: Numeric + Copy> Index<u8> for $name<T> {
            type Output = T;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: u8) -> &T {
                &self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> IndexMut<u8> for $name<T> {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: u8) -> &mut T {
                &mut self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> Index<u32> for $name<T> {
            type Output = T;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: u32) -> &T {
                &self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> IndexMut<u32> for $name<T> {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: u32) -> &mut T {
                &mut self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> Index<i32> for $name<T> {
            type Output = T;
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, i: i32) -> &T {
                &self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> IndexMut<i32> for $name<T> {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn index_mut(&mut self, i: i32) -> &mut T {
                &mut self.0[i as usize]
            }
        }
        impl<T: Numeric + Copy> Index<RangeFull> for $name<T> {
            type Output = [T];
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn index(&self, r: RangeFull) -> &[T] {
                &self.0[r]
            }
        }
        impl<T: Numeric + Copy> $name<T> {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn from_vec(x: Vec<T>) -> $name<T> {
                debug_assert_eq!(x.len(), $l);
                let mut tmp = [<T>::default(); $l];
                for (i, e) in x.iter().enumerate() {
                    tmp[i] = *e;
                }
                $name(tmp.clone())
            }

            // We can't use the [From] trait here because otherwise it would conflict with
            // the From<T> for T core implementation, as the array also implements the [SeqTrait].
            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            pub fn from_seq<U: SeqTrait<T>>(x: &U) -> $name<T> {
                debug_assert_eq!(x.len(), $l);
                let mut out = $name::new();
                for i in 0..x.len() {
                    out[i] = x[i];
                }
                out
            }
        }

        /// **Warning:** declassifies secret integer types.
        impl<T: Numeric + Copy> fmt::Debug for $name<T> {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..].iter().collect::<Vec<_>>().fmt(f)
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
/// This creates arrays for secret integers, i.e. `$t` is the secret integer
/// type and `$tbase` is the according Rust type.
macro_rules! _secret_array {
    ($name:ident,$l:expr,$t:ty, $tbase:ty) => {
        _array_base!($name, $l, $t);

        /// **Warning:** declassifies secret integer types.
        impl fmt::Debug for $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..]
                    .iter()
                    .map(|x| <$t>::declassify(*x))
                    .collect::<Vec<_>>()
                    .fmt(f)
            }
        }
        /// **Warning:** declassifies secret integer types.
        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn declassify_eq(&self, other: &Self) -> bool {
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
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
            pub fn to_be_bytes(&self) -> Seq<U8> {
                const FACTOR: usize = core::mem::size_of::<$t>();
                let mut out: Seq<U8> = Seq::new($l * FACTOR);
                for i in 0..$l {
                    let tmp: $t = self[i];
                    let tmp = <$t>::to_be_bytes(&[tmp]);
                    for j in 0..FACTOR {
                        out[i * FACTOR + j] = tmp[j];
                    }
                }
                out
            }

            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_le_bytes(&self) -> Seq<U8> {
                const FACTOR: usize = core::mem::size_of::<$t>();
                let mut out: Seq<U8> = Seq::new($l * FACTOR);
                for i in 0..$l {
                    let tmp: $t = self[i];
                    let tmp = <$t>::to_le_bytes(&[tmp]);
                    for j in 0..FACTOR {
                        out[i * FACTOR + j] = tmp[j];
                    }
                }
                out
            }
        }
        impl $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn from_public_slice(v: &[$tbase]) -> $name {
                debug_assert!(v.len() == $l);
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$t>::classify(*x))
                        .collect::<Vec<$t>>(),
                )
            }

            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn to_public_array(&self) -> [$tbase; $l] {
                let mut out = [0; $l];
                for (x, o) in self.0.iter().zip(out.iter_mut()) {
                    *o = <$t>::declassify(*x);
                }
                out
            }

            /// Create an array from a regular Rust array.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec_lib::prelude::*;
            ///
            /// bytes!(Block, 5);
            /// let b = Block::from_public_array([1, 2, 3, 4, 5]);
            /// ```
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
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
#[doc(hidden)]
macro_rules! _public_array {
    ($name:ident,$l:expr,$t:ty) => {
        _array_base!($name, $l, $t);

        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn into_le_bytes(self) -> Seq<u8> {
                const FACTOR: usize = core::mem::size_of::<$t>();
                let mut out: Seq<u8> = Seq::new($l * FACTOR);
                for i in 0..$l {
                    let tmp = <$t>::to_le_bytes(self[i]);
                    for j in 0..FACTOR {
                        out[i * FACTOR + j] = tmp[j];
                    }
                }
                out
            }
        }

        impl fmt::Debug for $name {
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0[..].fmt(f)
            }
        }
        impl PartialEq for $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            fn eq(&self, other: &Self) -> bool {
                self.0[..] == other.0[..]
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_secret_u8_array {
    ($name:ident, $l:expr) => {
        _secret_array!($name, $l, U8, u8);
        _implement_numeric_unsigned_secret!($name, U8);

        impl $name {
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_be_U32s(&self) -> Seq<U32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = U32_from_be_bytes(U32Word::from_native_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_le_U32s(&self) -> Seq<U32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = U32_from_le_bytes(U32Word::from_native_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_be_U64s(&self) -> Seq<U64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = U64_from_be_bytes(U64Word::from_native_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_le_U64s(&self) -> Seq<U64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = U64_from_le_bytes(U64Word::from_native_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_U128s_be(&self) -> Seq<U128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = U128_from_be_bytes(U128Word::from_native_slice(block));
                }
                out
            }
            #[allow(non_snake_case)]
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_U128s_le(&self) -> Seq<U128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = U128_from_le_bytes(U128Word::from_native_slice(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn to_hex(&self) -> String {
                let strs: Vec<String> = self.0.iter().map(|b| format!("{:02x}", b)).collect();
                strs.join("")
            }
        }
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! _implement_public_u8_array {
    ($name:ident, $l:expr) => {
        _public_array!($name, $l, u8);
        _implement_numeric_unsigned_public!($name);

        impl $name {
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_be_u32s(&self) -> Seq<u32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = u32::from_be_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_le_u32s(&self) -> Seq<u32> {
                let mut out = Seq::new($l / 4);
                for (i, block) in self.0.chunks(4).enumerate() {
                    debug_assert!(block.len() == 4);
                    out[i] = u32::from_le_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_be_u64s(&self) -> Seq<u64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = u64::from_be_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_le_u64s(&self) -> Seq<u64> {
                let mut out = Seq::new($l / 8);
                for (i, block) in self.0.chunks(8).enumerate() {
                    debug_assert!(block.len() == 8);
                    out[i] = u64::from_le_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_u128s_be(&self) -> Seq<u128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = u128::from_be_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
            pub fn to_u128s_le(&self) -> Seq<u128> {
                let mut out = Seq::new($l / 16);
                for (i, block) in self.0.chunks(16).enumerate() {
                    debug_assert!(block.len() == 16);
                    out[i] = u128::from_le_bytes(to_array(block));
                }
                out
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec($name))]
            pub fn to_hex(&self) -> String {
                let strs: Vec<String> = self.0.iter().map(|b| format!("{:02x}", b)).collect();
                strs.join("")
            }
        }
    };
}

// The following are the macros intended for use from the outside.

#[macro_export]
/// Create a new array with the given name, length, and type.
macro_rules! array {
    ($name:ident, $l:expr, U8) => {
        _implement_secret_u8_array!($name, $l);
    };
    ($name:ident, $l:expr, U8, $idx: ident) => {
        _implement_secret_u8_array!($name, $l);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, U16) => {
        _secret_array!($name, $l, U16, u16);
        _implement_numeric_unsigned_secret!($name, U16);
    };
    ($name:ident, $l:expr, U16, type_for_indexes: $idx: ident) => {
        _secret_array!($name, $l, U16, u16);
        _implement_numeric_unsigned_secret!($name, U16);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, U32) => {
        _secret_array!($name, $l, U32, u32);
        _implement_numeric_unsigned_secret!($name, U32);
    };
    ($name:ident, $l:expr, U32, type_for_indexes: $idx: ident) => {
        _secret_array!($name, $l, U32, u32);
        _implement_numeric_unsigned_secret!($name, U32);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, U64) => {
        _secret_array!($name, $l, U64, u64);
        _implement_numeric_unsigned_secret!($name, U64);
    };
    ($name:ident, $l:expr, U64, type_for_indexes: $idx: ident) => {
        _secret_array!($name, $l, U64, u64);
        _implement_numeric_unsigned_secret!($name, U64);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, U128) => {
        _secret_array!($name, $l, U128, u128);
        _implement_numeric_unsigned_secret!($name, U128);
    };
    ($name:ident, $l:expr, U128, type_for_indexes: $idx: ident) => {
        _secret_array!($name, $l, U128, u128);
        _implement_numeric_unsigned_secret!($name, U128);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, u8) => {
        _implement_public_u8_array!($name, $l);
    };
    ($name:ident, $l:expr, u8, type_for_indexes: $idx: ident) => {
        _implement_public_u8_array!($name, $l);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, u16) => {
        _public_array!($name, $l, u16);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u16, type_for_indexes: $idx: ident) => {
        _public_array!($name, $l, u16);
        _implement_numeric_unsigned_public!($name);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, u32) => {
        _public_array!($name, $l, u32);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u32, type_for_indexes: $idx: ident) => {
        _public_array!($name, $l, u32);
        _implement_numeric_unsigned_public!($name);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, u64) => {
        _public_array!($name, $l, u64);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u64, type_for_indexes: $idx: ident) => {
        _public_array!($name, $l, u64);
        _implement_numeric_unsigned_public!($name);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, u128) => {
        _public_array!($name, $l, u128);
        _implement_numeric_unsigned_public!($name);
    };
    ($name:ident, $l:expr, u128, type_for_indexes: $idx: ident) => {
        _public_array!($name, $l, u128);
        _implement_numeric_unsigned_public!($name);
        pub type $idx = usize;
    };
    ($name:ident, $l:expr, $t:ty) => {
        _public_array!($name, $l, $t);
    };
    ($name:ident, $l:expr, $t:ty, type_for_indexes: $idx: ident) => {
        _public_array!($name, $l, $t);
        pub type $idx = usize;
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
macro_rules! secret_array {
    ( $int_type: ident, [ $( $x:expr ),+ ] ) => {
        [
            $(
                $int_type($x)
            ),+
        ]
    }
}

#[macro_export]
macro_rules! secret_bytes {
    ([ $( $x:expr ),+ ] ) => {
        secret_array!(U8, [$($x),+])
    }
}

#[macro_export]
macro_rules! assert_secret_array_eq {
    ( $a1: expr, $a2: expr, $si: ident) => {
        assert_eq!(
            $a1.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>(),
            $a2.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>()
        );
    };
}

#[macro_export]
macro_rules! assert_bytes_eq {
    ( $a1: expr, $a2: expr) => {
        assert_secret_array_eq!($a1, $a2, U8)
    };
}

#[macro_export]
macro_rules! both_arrays {
    ($public_name:ident, $name:ident, $l:expr, $t:ty, $tbase:ty) => {
        _secret_array!($name, $l, $t, $tbase);
        _public_array!($public_name, $l, $tbase);

        impl $name {
            /// Conversion function between public and secret array versions.
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
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
            #[cfg_attr(feature = "use_attributes", unsafe_hacspec($name))]
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
