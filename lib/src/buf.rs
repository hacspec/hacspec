//! # hacspec buffer
//!
//! A buffer for operating on hacspec bytes.

use std::collections::VecDeque;

use super::seq::*;
use crate::prelude::*;

#[derive(Debug, Clone)]
pub struct ByteBuffer {
    value: VecDeque<Bytes>,
}

impl ByteBuffer {
    /// Create an empty buffer.
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    pub fn new() -> ByteBuffer {
        Self {
            value: VecDeque::new(),
        }
    }

    /// Create a buffer from [`Bytes`].
    #[cfg_attr(feature = "use_attributes", in_hacspec)]
    pub fn from_seq(seq: Bytes) -> ByteBuffer {
        let mut value: VecDeque<Bytes> = VecDeque::with_capacity(1);
        value.push_back(seq);
        Self { value }
    }

    /// Add a new chunk of [`Bytes`] to this [`ByteBuffer`].
    #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
    pub fn concat_owned(mut self, seq: Bytes) -> ByteBuffer {
        self.value.push_back(seq);
        self
    }

    /// Split off `num` bytes and return the [`Bytes`].
    #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
    pub fn split_off(mut self, len: usize) -> (Bytes, ByteBuffer) {
        assert!(self.value.len() != 0, "The buffer is empty.");

        if len == self.value[0].len() {
            // This is the efficient case.
            let val = self.value.pop_front().unwrap();
            (val, self)
        } else {
            // Here we don't optimize and just take the first len bytes.
            let mut out = self.value.pop_front().unwrap();
            assert!(out.len() != len);
            if out.len() > len {
                let (full_out, to_keep) = out.split_off(len);
                out = full_out;
                self.value.push_front(to_keep);
                return (out, self);
            } else {
                assert!(out.len() < len);
                // Get more bytes until we have enough.
                while out.len() < len {
                    let next = self.value.pop_front().unwrap();
                    if next.len() <= (len - out.len()) {
                        out = out.concat_owned(next);
                    } else {
                        let (next, to_keep) = next.split_off(len - out.len());
                        out = out.concat_owned(next);
                        self.value.push_front(to_keep);
                    }
                }
                return (out, self);
            }
        }
    }

    /// Get the buffer a single [`Bytes`] object (not efficient).
    #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
    pub fn to_bytes(&self) -> Bytes {
        let mut out = Bytes::new(0);
        for value in self.value.iter() {
            out = out.concat_owned(value.clone());
        }
        out
    }

    /// Get the buffer a single [`Bytes`] object (efficient, consuming the buffer).
    #[cfg_attr(feature = "use_attributes", unsafe_hacspec)]
    pub fn into_bytes(mut self) -> Bytes {
        self.value
            .drain(..)
            .fold(Bytes::new(0), |acc, next| acc.concat_owned(next))
    }
}

// === Helper functions not in hacspec === //

impl ByteBuffer {}
