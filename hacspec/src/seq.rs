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
            // Running index used when data is pushed into a Seq.
            pub(crate) idx: usize,
        }
        declare_seq_with_contents_constraints_impl!($name, Copy + Default + $constraint);
    };
    ($name:ident) => {
        /// Variable length byte arrays.
        #[derive(Debug, Clone, Default)]
        pub struct $name<T: Copy + Default> {
            pub(crate) b: Vec<T>,
            // Running index used when data is pushed into a Seq.
            pub(crate) idx: usize,
        }

        declare_seq_with_contents_constraints_impl!($name, Copy + Default);
    };
}

macro_rules! declare_seq_with_contents_constraints_impl {
    ($name:ident, $bound:tt $(+ $others:tt )*) => {

        impl<T: $bound $(+ $others)*> $name<T> {
            /// Get a new sequence of capacity `l`.
            pub fn new(l: usize) -> Self {
                Self {
                    b: vec![T::default(); l],
                    idx: 0,
                }
            }
            /// Get a new sequence from array `v`.
            pub fn from_array(v: &[T]) -> Self {
                Self {
                    b: v.to_vec(),
                    idx: 0,
                }
            }
            /// Get the size of this sequence.
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
            pub fn update<A: SeqTrait<T>>(self, start: usize, v: A) -> Self {
                println!("{:?} >= {:?} + {:?}", self.len(), start, v.len());
                debug_assert!(self.len() >= start + v.len());
                let mut self_copy = self;
                for (i, b) in v.iter().enumerate() {
                    self_copy[start + i] = *b;
                }
                self_copy
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
            pub fn update_sub<A: SeqTrait<T>>(
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
            /// Update this sequence with `v` at position `start_out`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// s = s.update_element(4, 7);
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 0, 0, 7]));
            /// ```
            pub fn update_element(mut self, start_out: usize, v: T) -> Self {
                debug_assert!(self.len() >= start_out + 1);
                self[start_out] = v;
                self
            }
            /// Reset the sequence index.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// s = s.set_index(3);
            /// s = s.push(Seq::<u8>::from_array(&[4, 5]));
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 0, 4, 5]));
            /// ```
            pub fn set_index(self, i: usize) -> Self {
                Self {
                    b: self.b.clone(),
                    idx: i,
                }
            }
            /// Push `v` to this sequence and move `idx` according to `v.len()`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// s = s.set_index(3);
            /// s = s.push(Seq::<u8>::from_array(&[4, 5]));
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 0, 4, 5]));
            /// ```
            pub fn push<A: SeqTrait<T>>(self, v: A) -> Self {
                println!("{:?} >= {:?} + {:?}", self.len(), self.idx, v.len());
                debug_assert!(self.len() >= self.idx + v.len());
                let idx = self.idx;
                let mut self_copy = self;
                for (i, b) in v.iter().enumerate() {
                    self_copy[idx + i] = *b;
                }
                self_copy.idx += v.len();
                self_copy
            }
            /// Push `l` elements from `v` to this sequence and move `idx` according to `l`.
            ///
            /// # Examples
            ///
            /// ```
            /// use hacspec::prelude::*;
            ///
            /// let mut s = Seq::<u8>::new(5);
            /// s = s.set_index(3);
            /// s = s.push_sub(Seq::<u8>::from_array(&[4, 5]), 1, 1);
            /// // assert_eq!(s, Seq::<u8>::from_array(&[0, 0, 0, 5, 0]));
            /// ```
            pub fn push_sub<A: SeqTrait<T>>(self, v: A, start: usize, l: usize) -> Self {
                debug_assert!(self.len() >= self.idx + l);
                debug_assert!(v.len() >= start + l);
                let idx = self.idx;
                let mut self_copy = self;
                for (i, b) in v.iter().skip(start).take(l).enumerate() {
                    self_copy[idx + i] = *b;
                }
                self_copy.idx += l;
                self_copy
            }
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

            pub fn from_sub<A: SeqTrait<T>>(input: A, r: Range<usize>) -> Self {
                let mut a = Self::default();
                for (i, v) in r
                    .clone()
                    .zip(input.iter().skip(r.start).take(r.end - r.start))
                {
                    a[i] = *v;
                }
                a
            }

            pub fn chunks<'a>(
                &'a self,
                chunk_size: usize,
            ) -> impl Iterator<Item = (usize, Seq<T>)> + 'a {
                self.b
                    .chunks(chunk_size)
                    .map(|c| (c.len(), Seq::<T>::from_slice(c)))
            }
        }

        impl<T: $bound $(+ $others)*> SeqTrait<T> for $name<T> {
            fn len(&self) -> usize {
                self.b.len()
            }
            fn iter(&self) -> std::slice::Iter<T> {
                self.b.iter()
            }
        }

        impl<T: $bound $(+ $others)*> Index<u8> for $name<T> {
            type Output = T;
            fn index(&self, i: u8) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u8> for $name<T> {
            fn index_mut(&mut self, i: u8) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<u32> for $name<T> {
            type Output = T;
            fn index(&self, i: u32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<u32> for $name<T> {
            fn index_mut(&mut self, i: u32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<i32> for $name<T> {
            type Output = T;
            fn index(&self, i: i32) -> &T {
                &self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<i32> for $name<T> {
            fn index_mut(&mut self, i: i32) -> &mut T {
                &mut self.b[i as usize]
            }
        }

        impl<T: $bound $(+ $others)*> Index<usize> for $name<T> {
            type Output = T;
            fn index(&self, i: usize) -> &T {
                &self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> IndexMut<usize> for $name<T> {
            fn index_mut(&mut self, i: usize) -> &mut T {
                &mut self.b[i]
            }
        }

        impl<T: $bound $(+ $others)*> Index<Range<usize>> for $name<T> {
            type Output = [T];
            fn index(&self, r: Range<usize>) -> &[T] {
                &self.b[r]
            }
        }

        impl<T: $bound $(+ $others)*> $name<T> {
            pub fn from_vec(x: Vec<T>) -> $name<T> {
                Self {
                    b: x.clone(),
                    idx: 0,
                }
            }

            pub fn from_slice(x: &[T]) -> $name<T> {
                Self {
                    b: x.to_vec(),
                    idx: 0,
                }
            }

            pub fn from_seq<U: SeqTrait<T>>(x: U) -> $name<T> {
                let mut tmp: Vec<T> = Vec::new();
                for e in x.iter() {
                    tmp.push(*e);
                }
                Self { b: tmp, idx: 0 }
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
    pub fn from_hex(s: &str) -> Seq<U8> {
        Seq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }

    pub fn from_string(s: String) -> Seq<U8> {
        Seq::<U8>::from_vec(
            hex_string_to_bytes(&s)
                .iter()
                .map(|x| U8::classify(*x))
                .collect::<Vec<_>>(),
        )
    }
}

impl PublicSeq<u8> {
    pub fn from_hex(s: &str) -> PublicSeq<u8> {
        PublicSeq::from_vec(
            hex_string_to_bytes(s)
                .iter()
                .map(|x| *x)
                .collect::<Vec<_>>(),
        )
    }

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
    fn get_random_vec(l: usize) -> Vec<U8> {
        (0..l)
            .map(|_| rand::random::<u8>())
            .map(|x| U8::classify(x))
            .collect()
    }

    pub fn random(l: usize) -> Self {
        Self {
            b: Seq::get_random_vec(l),
            idx: 0,
        }
    }

    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.b.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}

impl PublicSeq<u8> {
    pub fn to_hex(&self) -> String {
        let strs: Vec<String> = self.iter().map(|b| format!("{:02x}", b)).collect();
        strs.join("")
    }
}
