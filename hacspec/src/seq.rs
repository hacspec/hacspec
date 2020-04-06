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
        pub struct $name<T: Copy + Default + $constraint> {
            pub(crate) b: Vec<T>,
        }
        declare_seq_with_contents_constraints_impl!($name, Copy + Default + $constraint);
    };
    ($name:ident) => {
        /// Variable length byte arrays.
        #[derive(Debug, Clone, Default)]
        pub struct $name<T: Copy + Default> {
            pub(crate) b: Vec<T>,
        }

        declare_seq_with_contents_constraints_impl!($name, Copy + Default);
    };
}

macro_rules! declare_seq_with_contents_constraints_impl {
    ($name:ident, $bound:tt $(+ $others:tt )*) => {

        impl<T: $bound $(+ $others)*> $name<T> {
            /// Get a new sequence of capacity `l`.
            #[primitive(hacspec)]
            pub fn new(l: usize) -> Self {
                Self {
                    b: vec![T::default(); l],
                }
            }
            /// Get a new sequence from array `v`.
            // TODO: rename from_slice
            #[external(hacspec)]
            pub fn from_array(v: &[T]) -> Self {
                Self {
                    b: v.to_vec(),
                }
            }
            /// Get the size of this sequence.
            #[primitive(hacspec)]
            pub fn len(&self) -> usize {
                self.b.len()
            }
            /// Update this sequence with `v` starting at `start`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// let tmp = Seq::<u8>::from_array(&[2, 3]);
            /// s = s.update(2, tmp);
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 2, 3, 0]));
            /// ```
            #[library(hacspec)]
            pub fn update<A: SeqTrait<T>>(self, start: usize, v: A) -> Self {
                let len = v.len();
                self.update_sub(start, v, 0, len)
            }

            #[library(hacspec)]
            pub fn update_start<A: SeqTrait<T>>(
                self,
                v: A
            ) -> Self {
                let len = v.len();
                self.update_sub(0, v, 0, len)
            }

            #[primitive(hacspec)]
            pub fn sub(self, start_out: usize, len: usize) -> Self {
                Self::from_vec(
                    self.b
                        .iter()
                        .skip(start_out)
                        .map(|x| *x)
                        .take(len)
                        .collect::<Vec<T>>(),
                )
            }

            #[library(hacspec)]
            pub fn subr(self, r: Range<usize>) -> Self {
                self.sub(r.start, r.end - r.start)
            }

            #[library(hacspec)]
            pub fn from_sub<A: SeqTrait<T>>(input: A, r: Range<usize>) -> Self {
                let out_len = r.end - r.start;
                let mut a = Self::new(out_len);
                a = a.update_sub(0, input, r.start, out_len);
                a
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
            ) -> (usize, Self) {
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
            pub fn set_chunk<A: SeqTrait<T>>(
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

        impl<T: $bound $(+ $others)*> SeqTrait<T> for $name<T> {
            #[primitive(hacspec)]
            fn len(&self) -> usize {
                self.b.len()
            }
            #[primitive(hacspec)]
            fn iter(&self) -> std::slice::Iter<T> {
                self.b.iter()
            }

            /// Update this sequence with `l` elements of `v`, starting at `start_in`,
            /// at `start_out`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// let tmp = Seq::<u8>::from_array(&[2, 3]);
            /// s = s.update_sub(2, tmp, 1, 1);
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 3, 0, 0]));
            /// ```
            #[primitive(hacspec)]
            fn update_sub<A: SeqTrait<T>>(
                self,
                start_out: usize,
                v: A,
                start_in: usize,
                len: usize,
            ) -> Self {
                debug_assert!(self.len() >= start_out + len);
                debug_assert!(v.len() >= start_in + len);
                let mut self_copy = self;
                for (i, b) in v.iter().skip(start_in).take(len).enumerate() {
                    self_copy[start_out + i] = *b;
                }
                self_copy
            }
        }

        impl<T: $bound $(+ $others)*> Index<u8> for $name<T> {
            type Output = T;
            #[primitive(hacspec)]
            fn index(&self, i: u8) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u8> for $name<T> {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: u8) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<u32> for $name<T> {
            type Output = T;
            #[primitive(hacspec)]
            fn index(&self, i: u32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u32> for $name<T> {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: u32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<i32> for $name<T> {
            type Output = T;
            #[primitive(hacspec)]
            fn index(&self, i: i32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<i32> for $name<T> {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: i32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<usize> for $name<T> {
            type Output = T;
            #[primitive(hacspec)]
            fn index(&self, i: usize) -> &T {
                &self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<usize> for $name<T> {
            #[primitive(hacspec)]
            fn index_mut(&mut self, i: usize) -> &mut T {
                &mut self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> Index<Range<usize>> for $name<T> {
            type Output = [T];
            #[primitive(hacspec)]
            fn index(&self, r: Range<usize>) -> &[T] {
                &self.b[r]
            }
        }

        impl<T: $bound $(+ $others)*> $name<T> {
            #[external(hacspec)]
            pub fn from_vec(x: Vec<T>) -> $name<T> {
                Self {
                    b: x.clone(),
                }
            }

            #[external(hacspec)]
            pub fn from_slice(x: &[T]) -> $name<T> {
                Self {
                    b: x.to_vec(),
                }
            }

            #[primitive(hacspec)]
            pub fn from_seq<U: SeqTrait<T>>(x: U) -> $name<T> {
                let mut tmp: Vec<T> = Vec::new();
                for e in x.iter() {
                    tmp.push(*e);
                }
                Self { b: tmp }
            }
        }
    };
}

declare_seq!(SecretSeq, SecretInteger);
declare_seq!(PublicSeq, PublicInteger);
declare_seq!(Seq);

pub type ByteSeq = Seq<U8>;

/// Read hex string to Bytes.
impl Seq<U8> {
    #[primitive(hacspec)]
    pub fn from_hex(s: &str) -> Seq<U8> {
        Seq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }

    #[external(hacspec)]
    pub fn from_string(s: String) -> Seq<U8> {
        Seq::<U8>::from_vec(
            hex_string_to_bytes(&s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }
}

impl PartialEq for Seq<U8> {
    #[external(hacspec)]
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

impl PublicSeq<u8> {
    #[primitive(hacspec)]
    pub fn from_hex(s: &str) -> PublicSeq<u8> {
        PublicSeq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| *x)
                .collect::<Vec<_>>(),
        )
    }

    #[external(hacspec)]
    pub fn from_string(s: String) -> PublicSeq<u8> {
        PublicSeq::<u8>::from_vec(
            hex_string_to_bytes(&s)
                .iter()
                .map(|x| *x)
                .collect::<Vec<_>>(),
        )
    }
}

impl Seq<U8> {
    #[external(hacspec)]
    fn get_random_vec(l: usize) -> Vec<U8> {
        (0..l)
            .map(|_| rand::random::<u8>())
            .map(|x| U8::classify(x))
            .collect()
    }

    #[primitive(hacspec)]
    pub fn random(l: usize) -> Self {
        Self {
            b: Seq::get_random_vec(l),
        }
    }

    #[external(hacspec)]
    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.b.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}

impl PublicSeq<u8> {
    #[external(hacspec)]
    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}
