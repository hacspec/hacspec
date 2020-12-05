mod provider;
pub use provider::Chacha20Poly1305Evercrypt;

fn clone_into_array<A, T>(slice: &[T]) -> A
where
    A: Default + AsMut<[T]>,
    T: Clone,
{
    let mut a = Default::default();
    A::as_mut(&mut a).clone_from_slice(slice);
    a
}
