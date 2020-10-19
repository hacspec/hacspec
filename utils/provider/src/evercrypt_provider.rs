use super::{chacha20poly1305_trait::*, *};
use evercrypt::prelude::*;

pub struct Chacha20Poly1305_Evercrypt {}

impl Chacha20Poly1305 for Chacha20Poly1305_Evercrypt {
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
        clone_into_array(&aead_key_gen(AeadMode::Chacha20Poly1305))
    }
    fn nonce_gen(&self) -> [u8; 12] {
        aead_nonce_gen(AeadMode::Chacha20Poly1305)
    }

    // Single-shot encryption/decryption.
    fn encrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        m: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), Error> {
        let (ctxt, tag) = Aead::new(AeadMode::Chacha20Poly1305, key)
            .unwrap()
            .encrypt(m, nonce, aad)
            .unwrap();
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
        let mut n = [0u8; 12];
        let ctxt = match Aead::new(AeadMode::Chacha20Poly1305, key)
            .unwrap()
            .decrypt(c, tag, nonce, aad)
        {
            Ok(c) => c,
            Err(e) => return Err(format!("Error: {:?}", e)),
        };
        Ok(ctxt)
    }
}
