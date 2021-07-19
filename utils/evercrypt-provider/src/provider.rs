use aead::{
    consts::{U0, U12, U16, U32},
    generic_array::{ArrayLength, GenericArray},
    Error,
};
pub use aead::{Aead, AeadCore, AeadInPlace, NewAead, Payload};
use evercrypt::aead::{key_gen, nonce_gen, Aead as EvercryptAead, Mode};

pub struct Chacha20Poly1305 {
    aead: Option<EvercryptAead>,
}

impl Chacha20Poly1305 {
    pub fn key_gen() -> Key {
        Key::clone_from_slice(&key_gen(Mode::Chacha20Poly1305))
    }
    pub fn nonce_gen() -> Nonce {
        Nonce::clone_from_slice(&nonce_gen(Mode::Chacha20Poly1305))
    }
}

pub type Key = GenericArray<u8, U32>;
pub type Nonce = GenericArray<u8, U12>;
pub type Tag = GenericArray<u8, U16>;

impl NewAead for Chacha20Poly1305 {
    type KeySize = U32;

    fn new(key: &Key) -> Self {
        let aead = EvercryptAead::new(Mode::Chacha20Poly1305, key).ok();
        Self { aead }
    }
}

impl AeadCore for Chacha20Poly1305 {
    type NonceSize = U12;
    type TagSize = U16;
    type CiphertextOverhead = U0;
}

impl AeadInPlace for Chacha20Poly1305 {
    fn encrypt_in_place_detached(
        &self,
        nonce: &Nonce,
        associated_data: &[u8],
        buffer: &mut [u8],
    ) -> Result<Tag, Error> {
        let (ctxt, tag) = match &self.aead {
            Some(cipher) => match cipher.encrypt(buffer, &nonce, associated_data) {
                Ok(r) => r,
                Err(_) => return Err(Error),
            },
            None => return Err(Error),
        };
        buffer
            .iter_mut()
            .zip(ctxt.iter())
            .for_each(|(dst, &src)| *dst = src);
        Ok(Tag::clone_from_slice(&tag))
    }
    fn decrypt_in_place_detached(
        &self,
        nonce: &Nonce,
        associated_data: &[u8],
        buffer: &mut [u8],
        tag: &Tag,
    ) -> Result<(), Error> {
        let tag: Tag = into_array(&tag);
        let ptxt = match &self.aead {
            Some(cipher) => match cipher.decrypt(buffer, &tag, &nonce, associated_data) {
                Ok(r) => r,
                Err(_) => return Err(Error),
            },
            None => return Err(Error),
        };
        buffer
            .iter_mut()
            .zip(ptxt.iter())
            .for_each(|(dst, &src)| *dst = src);
        Ok(())
    }
}

// GenericArray to arrays.

fn into_array<A, T, N>(ga: &GenericArray<T, N>) -> A
where
    A: Default + AsMut<[T]>,
    T: Clone,
    N: ArrayLength<T>,
{
    let mut a = Default::default();
    A::as_mut(&mut a).clone_from_slice(ga.as_slice());
    a
}
