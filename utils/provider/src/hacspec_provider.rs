use hacspec_chacha20::{Key as HacspecKey, IV as HacspecNonce};
use hacspec_chacha20poly1305::{decrypt, encrypt};
use hacspec_lib::*;
use hacspec_poly1305::Tag as HacspecTag;

use super::{chacha20poly1305_trait::*, *};
use evercrypt::prelude::*;

pub struct Chacha20Poly1305_Hacspec {}

impl Chacha20Poly1305 for Chacha20Poly1305_Hacspec {
    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }
    fn get_instance(&self) -> Box<dyn Chacha20Poly1305> {
        Box::new(Self {})
    }

    // Nonce and key generation helper.
    fn key_gen(&self) -> [u8; 32] {
        get_random_array()
    }
    fn nonce_gen(&self) -> [u8; 12] {
        get_random_array()
    }

    // Single-shot encryption/decryption.
    fn encrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        m: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), Error> {
        let (ctxt, tag) = encrypt(
            HacspecKey::from_public_slice(key),
            HacspecNonce::from_public_slice(nonce),
            &ByteSeq::from_public_slice(aad),
            &ByteSeq::from_public_slice(m),
        );
        let ctxt = ctxt.iter().map(|b| b.declassify()).collect();
        let tag = clone_into_array(&tag.iter().map(|&b| b).collect::<Vec<u8>>());
        Ok((ctxt, tag))
    }

    fn decrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        c: &[u8],
        tag: &[u8; 16],
    ) -> Result<Vec<u8>, String> {
        let (msg, valid) = decrypt(
            HacspecKey::from_public_slice(key),
            HacspecNonce::from_public_slice(nonce),
            &ByteSeq::from_public_slice(aad),
            &ByteSeq::from_public_slice(c),
            HacspecTag::from_native_slice(tag),
        );
        let msg = msg.iter().map(|b| b.declassify()).collect();
        if valid {
            Ok(msg)
        } else {
            Err("Error decrypting.".to_string())
        }
    }
}
