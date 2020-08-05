use hacspec::prelude::*;
use rand::{Rng, AsByteSliceMut};

/// Random public byte
pub fn random_public_byte() -> u8 {
    let random_byte = rand::thread_rng().gen::<u8>();
    random_byte
}

/// Random byte
pub fn random_byte() -> U8 {
    random_public_byte().into()
}

/// Random array
pub fn random_bytes<A: Default + AsByteSliceMut>() -> A {
    let mut out = A::default();
    rand::thread_rng().fill(&mut out);
    out
}

/// Random vector
pub fn random_byte_vec(len: usize) -> Vec<u8> {
    (0..len).map(|_| rand::random::<u8>()).collect()
}
