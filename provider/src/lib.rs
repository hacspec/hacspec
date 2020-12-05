use rand::{self, AsByteSliceMut};
use rand_core::{OsRng, RngCore};

mod provider;
pub mod traits;
pub use provider::Chacha20Poly1305Hacspec;

fn clone_into_array<A, T>(slice: &[T]) -> A
where
    A: Default + AsMut<[T]>,
    T: Clone,
{
    let mut a = Default::default();
    A::as_mut(&mut a).clone_from_slice(slice);
    a
}

/// Generate a random byte vector of length `len`.
pub fn get_random_vec(len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    OsRng.fill_bytes(out.as_byte_slice_mut());
    out
}

/// Generate a random array.
pub fn get_random_array<A: Default + AsByteSliceMut>() -> A {
    let mut out = A::default();
    OsRng.fill_bytes(out.as_byte_slice_mut());
    out
}
