//!
//! # Sequences
//!
//! This module implements variable-length sequences and utility functions for it.
//! Seq only supports operations that are safe on secret values.
//! For use with public values you can use `PublicSeq`.
//!

use crate::prelude::*;

macro_rules! declare_seq {
    ($name:ident, $constraint:ident) => {
        /// Variable length byte arrays.
        #[derive(Debug, Clone, Default)]
        pub struct $name<T: Default + $constraint> {
            pub(crate) b: Vec<T>,
        }
        declare_seq_with_contents_constraints_impl!($name, Clone + Default + $constraint);
    };
    ($name:ident) => {
        /// Variable length byte arrays.
        #[derive(Debug, Clone, Default)]
        pub struct $name<T: Default> {
            pub(crate) b: Vec<T>,
        }

        declare_seq_with_contents_constraints_impl!($name, Clone + Default);
    };
}

macro_rules! declare_seq_with_contents_constraints_impl {
    ($name:ident, $bound:tt $(+ $others:tt )*) => {

        impl<T: $bound $(+ $others)*> $name<T> {
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            pub fn new(l: usize) -> Self {
                Self {
                    b: vec![T::default(); l],
                }
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            pub fn with_capacity(l: usize) -> Self {
                Self {
                    b: Vec::with_capacity(l),
                }
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            #[inline(always)]
            pub fn reserve(mut self, additional: usize) -> Self {
                self.b.reserve(additional);
                self
            }

            /// Get the size of this sequence.
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            pub fn len(&self) -> usize {
                self.b.len()
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn slice(&self, start_out: usize, len: usize) -> Self {
                Self::from_slice(self, start_out, len)
            }

            #[cfg_attr(feature="use_attributes", not_hacspec)]
            pub fn native_slice(&self) -> &[T] {
                &self.b
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            pub fn into_slice(mut self, start_out: usize, len: usize) -> Self {
                self.b = self.b.drain(start_out..start_out+len).collect();
                self
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn slice_range(&self, r: Range<usize>) -> Self {
                self.slice(r.start, r.end - r.start)
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            pub fn into_slice_range(mut self, r: Range<usize>) -> Self {
                self.b = self.b.drain(r).collect();
                self
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            #[inline(always)]
            pub fn split_off(mut self, at: usize) -> (Self, Self) {
                let other = Self::from_vec(self.b.split_off(at));
                (self, other)
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            #[inline(always)]
            pub fn truncate(mut self, len: usize) -> Self  {
                self.b.truncate(len);
                self
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn from_slice<A: SeqTrait<T>>(input: &A, start: usize, len: usize) -> Self {
                let mut a = Self::new(len);
                a = a.update_slice(0, input, start, len);
                a
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn concat<A: SeqTrait<T>>(&self, next: &A) -> Self {
                let mut out = Self::new(self.len() + next.len());
                out = out.update_start(self);
                out = out.update_slice(self.len(), next, 0, next.len());
                out
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            #[inline(always)]
            pub fn concat_owned(mut self, mut next: Self) -> Self {
                self.b.append(&mut next.b);
                self
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn push(&self, next: &T) -> Self {
                let mut out = Self::new(self.len() + 1);
                out = out.update_start(self);
                out[self.len()] = next.clone();
                out
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn push_owned(mut self, next: T) -> Self {
                self.b.push(next);
                self
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn from_slice_range<A: SeqTrait<T>>(input: &A, r: Range<usize>) -> Self {
                Self::from_slice(input, r.start, r.end - r.start)
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn num_chunks(
                &self,
                chunk_size: usize
            ) -> usize {
                (self.len() + chunk_size - 1) / chunk_size
            }

            /// Get the number of chunks of `chunk_size` in this array.
            /// There might be less than `chunk_size` remaining elements in this
            /// array beyond these.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn num_exact_chunks(&self, chunk_size: usize) -> usize {
                self.len() / chunk_size
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn get_chunk(
                &self,
                chunk_size: usize,
                chunk_number: usize
            ) -> (usize, Self) {
                let idx_start = chunk_size * chunk_number;
                let len = if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                };
                let out = self.slice(idx_start, len);
                (len, out)
            }

            /// Get the `chunk_number` chunk of `chunk_size` from this array
            /// as `Seq<T>`.
            /// The resulting sequence is of exactly `chunk_size` length.
            /// Until #84 is fixed this returns an empty sequence if not enough
            /// elements are left.
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn get_exact_chunk(&self, chunk_size: usize, chunk_number: usize) -> Self {
                let (len, chunk) = self.get_chunk(chunk_size, chunk_number);
                if len != chunk_size {
                   Self::new(0)
                } else {
                    chunk
                }
            }

            /// Get the remaining chunk of this array of length less than
            /// `chunk_size`.
            /// If there's no remainder, i.e. if the length of this array can
            /// be divided by `chunk_size` without a remainder, the function
            /// returns an empty sequence (until #84 is fixed).
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn get_remainder_chunk(&self, chunk_size: usize) -> Self {
                let chunks = self.num_chunks(chunk_size);
                let last_chunk = if chunks > 0 {
                    chunks - 1
                } else {
                    0
                };
                let (len, chunk) = self.get_chunk(chunk_size, last_chunk);
                if len == chunk_size {
                    Self::new(0)
                } else {
                    chunk
                }
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn set_chunk<A: SeqTrait<T>>(
                self,
                chunk_size: usize,
                chunk_number: usize,
                input: &A,
            ) -> Self {
                let idx_start = chunk_size * chunk_number;
                let len = if idx_start + chunk_size > self.len() {
                    self.len() - idx_start
                } else {
                    chunk_size
                };
                debug_assert!(input.len() == len, "the chunk length should match the input. got {}, expected {}", input.len(), len);
                self.update_slice(idx_start, input, 0, len)
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn set_exact_chunk<A: SeqTrait<T>>(
                self,
                chunk_size: usize,
                chunk_number: usize,
                input: &A,
            ) -> Self {
                debug_assert!(input.len() == chunk_size, "the chunk length must match the chunk_size. got {}, expected {}", input.len(), chunk_size);
                let idx_start = chunk_size * chunk_number;
                debug_assert!(idx_start + chunk_size <= self.len(), "not enough space for a full chunk. space left: {}, needed {}", input.len(), chunk_size);
                self.update_slice(idx_start, input, 0, chunk_size)
            }
        }

        impl<T: $bound $(+ $others)*> SeqTrait<T> for $name<T> {
            /// Get a new sequence of capacity `l`.
            #[cfg_attr(feature="use_attributes", in_hacspec)]
            fn create(l: usize) -> Self {
                Self::new(l)
            }

            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn len(&self) -> usize {
                self.b.len()
            }
            #[cfg_attr(feature="use_attributes", not_hacspec)]
            fn iter(&self) -> std::slice::Iter<T> {
                self.b.iter()
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec($name))]
            fn update_slice<A: SeqTrait<T>>(
                mut self,
                start_out: usize,
                v: &A,
                start_in: usize,
                len: usize,
            ) -> Self {
                debug_assert!(self.len() >= start_out + len, "{} < {} + {}", self.len(), start_out, len);
                debug_assert!(v.len() >= start_in + len, "{} < {} + {}", v.len(), start_in, len);
                for i in 0..len {
                    self[start_out + i] = v[start_in + i].clone();
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

        impl<T: $bound $(+ $others)*> Index<u8> for $name<T> {
            type Output = T;
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index(&self, i: u8) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u8> for $name<T> {
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index_mut(&mut self, i: u8) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<u32> for $name<T> {
            type Output = T;
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index(&self, i: u32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u32> for $name<T> {
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index_mut(&mut self, i: u32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<i32> for $name<T> {
            type Output = T;
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index(&self, i: i32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<i32> for $name<T> {
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index_mut(&mut self, i: i32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<usize> for $name<T> {
            type Output = T;
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index(&self, i: usize) -> &T {
                &self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<usize> for $name<T> {
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index_mut(&mut self, i: usize) -> &mut T {
                &mut self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> Index<Range<usize>> for $name<T> {
            type Output = [T];
            #[cfg_attr(feature="use_attributes", unsafe_hacspec)]
            fn index(&self, r: Range<usize>) -> &[T] {
                &self.b[r]
            }
        }

        impl<T: $bound $(+ $others)*> $name<T> {
            #[cfg_attr(feature="use_attributes", not_hacspec)]
            pub fn from_vec(b: Vec<T>) -> $name<T> {
                Self {
                    b,
                }
            }

            #[cfg_attr(feature="use_attributes", not_hacspec)]
            pub fn from_native_slice(x: &[T]) -> $name<T> {
                Self {
                    b: x.to_vec(),
                }
            }

            #[cfg_attr(feature="use_attributes", in_hacspec)]
            pub fn from_seq<U: SeqTrait<T>>(x: &U) -> $name<T> {
                let mut tmp = $name::new(x.len());
                for i in 0..x.len() {
                    tmp[i] = x[i].clone();
                }
                tmp
            }
        }
    };
}

declare_seq!(SecretSeq, SecretInteger);
declare_seq!(PublicSeq, PublicInteger);
declare_seq!(Seq);

pub type ByteSeq = Seq<U8>;
pub type PublicByteSeq = PublicSeq<u8>;

/// Read hex string to Bytes.
impl Seq<U8> {
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_hex(s: &str) -> Seq<U8> {
        Seq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }

    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_string(s: String) -> Seq<U8> {
        Seq::<U8>::from_vec(
            hex_string_to_bytes(&s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }
}

impl<T: Copy + Default + PartialEq + PublicInteger> PartialEq for PublicSeq<T> {
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn eq(&self, other: &Self) -> bool {
        self.b == other.b
    }
}

impl<T: Copy + Default + PartialEq + PublicInteger> Eq for PublicSeq<T> {}

impl PartialEq for Seq<U8> {
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    fn eq(&self, other: &Self) -> bool {
        self.b[..]
            .iter()
            .map(|x| <U8>::declassify(*x))
            .collect::<Vec<_>>()
            == other.b[..]
                .iter()
                .map(|x| <U8>::declassify(*x))
                .collect::<Vec<_>>()
    }
}

#[macro_export]
macro_rules! assert_secret_seq_eq {
    ( $a1: expr, $a2: expr, $si: ident) => {
        assert_eq!(
            $a1.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>(),
            $a2.iter().map(|x| $si::declassify(*x)).collect::<Vec<_>>()
        );
    };
}

impl PublicSeq<u8> {
    #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
    pub fn from_hex(s: &str) -> PublicSeq<u8> {
        PublicSeq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| *x)
                .collect::<Vec<_>>(),
        )
    }

    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn from_string(s: String) -> PublicSeq<u8> {
        PublicSeq::<u8>::from_vec(
            hex_string_to_bytes(&s)
                .iter()
                .map(|x| *x)
                .collect::<Vec<_>>(),
        )
    }
}

macro_rules! impl_from_public_slice {
    ($t:ty,$st:ty) => {
        impl Seq<$st> {
            #[cfg_attr(feature = "use_attributes", not_hacspec)]
            pub fn from_public_slice(v: &[$t]) -> Seq<$st> {
                Self::from_vec(
                    v[..]
                        .iter()
                        .map(|x| <$st>::classify(*x))
                        .collect::<Vec<$st>>(),
                )
            }

            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn from_public_seq<U: SeqTrait<$t>>(x: &U) -> Seq<$st> {
                let mut tmp = Self::new(x.len());
                for i in 0..x.len() {
                    tmp[i] = <$st>::classify(x[i]);
                }
                tmp
            }
        }
    };
}

impl_from_public_slice!(u8, U8);
impl_from_public_slice!(u16, U16);
impl_from_public_slice!(u32, U32);
impl_from_public_slice!(u64, U64);
impl_from_public_slice!(u128, U128);

macro_rules! impl_declassify {
    ($t:ty,$st:ty) => {
        impl Seq<$st> {
            #[cfg_attr(feature = "use_attributes", in_hacspec)]
            pub fn declassify(self) -> Seq<$t> {
                let mut tmp = <Seq<$t>>::new(self.len());
                for i in 0..self.len() {
                    tmp[i] = <$st>::declassify(self[i]);
                }
                tmp
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec)]
            pub fn into_native(self) -> Vec<$t> {
                self.b.iter().map(|&x| <$st>::declassify(x)).collect()
            }
            #[cfg_attr(feature = "use_attributes", not_hacspec)]
            pub fn to_native(&self) -> Vec<$t> {
                self.b.iter().map(|&x| <$st>::declassify(x)).collect()
            }
        }
    };
}

impl_declassify!(u8, U8);
impl_declassify!(u16, U16);
impl_declassify!(u32, U32);
impl_declassify!(u64, U64);
impl_declassify!(u128, U128);

impl Seq<U8> {
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.b.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}

impl PublicSeq<u8> {
    #[cfg_attr(feature = "use_attributes", not_hacspec)]
    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}

#[macro_export]
macro_rules! public_byte_seq {
    ($( $b:expr ),+) => {
        PublicByteSeq::from_vec(
            vec![
                $(
                    $b
                ),+
            ]
        )
    };
}

#[macro_export]
macro_rules! byte_seq {
    ($( $b:expr ),+) => {
        ByteSeq::from_vec(
            vec![
                $(
                    U8($b)
                ),+
            ]
        )
    };
}
