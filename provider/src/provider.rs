pub use aead::{self, AeadCore, AeadInPlace, Error, NewAead};
use aead::{
    consts::{U0, U12, U16, U32},
    generic_array::GenericArray,
};
use hacspec_chacha20::{Key as HacspecKey, IV};
use hacspec_chacha20poly1305::*;
use hacspec_lib::prelude::*;
use hacspec_poly1305::Tag as HacspecTag;

pub struct Chacha20Poly1305 {
    key: Key,
}

pub type Key = GenericArray<u8, U32>;
pub type Nonce = GenericArray<u8, U12>;
pub type Tag = GenericArray<u8, U16>;

impl NewAead for Chacha20Poly1305 {
    type KeySize = U32;

    fn new(key: &Key) -> Self {
        Self { key: *key }
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
        let nonce = IV::from_public_slice(&(nonce.as_slice()));
        let key = HacspecKey::from_public_slice(&self.key.as_slice());
        let (ctxt, tag) = encrypt(
            key,
            nonce,
            &ByteSeq::from_public_slice(&associated_data),
            &ByteSeq::from_public_slice(buffer),
        );

        buffer
            .iter_mut()
            .zip(ctxt.iter())
            .for_each(|(dst, &src)| *dst = src.declassify());
        let tag = Tag::clone_from_slice(&tag.iter().map(|&b| b).collect::<Vec<u8>>());
        Ok(tag)
    }

    fn decrypt_in_place_detached(
        &self,
        nonce: &Nonce,
        associated_data: &[u8],
        buffer: &mut [u8],
        tag: &Tag,
    ) -> Result<(), Error> {
        let (ptxt, valid) = decrypt(
            HacspecKey::from_public_slice(self.key.as_slice()),
            IV::from_public_slice(nonce),
            &ByteSeq::from_public_slice(associated_data),
            &ByteSeq::from_public_slice(buffer),
            HacspecTag::from_native_slice(tag),
        );

        buffer
            .iter_mut()
            .zip(ptxt.iter())
            .for_each(|(dst, &src)| *dst = src.declassify());
        if valid {
            Ok(())
        } else {
            Err(Error)
        }
    }
}
