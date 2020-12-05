use super::*;
use evercrypt::prelude::*;
use hacspec_provider::traits::*;

pub struct Chacha20Poly1305Evercrypt {}

impl Chacha20Poly1305 for Chacha20Poly1305Evercrypt {
    fn new() -> Self {
        Self {}
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
        let (ctxt, tag) = match Aead::new(AeadMode::Chacha20Poly1305, key) {
            Ok(cipher) => match cipher.encrypt(m, nonce, aad) {
                Ok(r) => r,
                Err(e) => return Err(Error(format!("Error: {:?}", e))),
            },
            Err(e) => return Err(Error(format!("Error: {:?}", e))),
        };
        Ok((ctxt, tag))
    }

    fn decrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        c: &[u8],
        tag: &[u8; 16],
    ) -> Result<Vec<u8>, Error> {
        let ptxt = match Aead::new(AeadMode::Chacha20Poly1305, key) {
            Ok(cipher) => match cipher.decrypt(c, tag, nonce, aad) {
                Ok(r) => r,
                Err(e) => return Err(Error(format!("Error: {:?}", e))),
            },
            Err(e) => return Err(Error(format!("Error: {:?}", e))),
        };
        Ok(ptxt)
    }
}
