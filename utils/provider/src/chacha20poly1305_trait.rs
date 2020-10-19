#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidInit = 0,
    InvalidAlgorithm = 1,
    InvalidCiphertext = 2,
    InvalidNonce = 3,
    UnsupportedConfig = 4,
    Encrypting = 5,
    Decrypting = 6,
}

pub trait Chacha20Poly1305 {
    fn new() -> Self
    where
        Self: Sized;
    fn get_instance(&self) -> Box<dyn Chacha20Poly1305>;

    // Nonce and key generation helper.
    fn key_gen(&self) -> [u8; 32];
    fn get_key_len(&self) -> usize {
        32
    }
    fn nonce_gen(&self) -> [u8; 12];
    fn get_nonce_len(&self) -> usize {
        12
    }

    // Single-shot encryption/decryption.
    fn encrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        m: &[u8],
    ) -> Result<(Vec<u8>, [u8; 16]), Error>;
    fn decrypt(
        &self,
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        c: &[u8],
        tag: &[u8; 16],
    ) -> Result<Vec<u8>, String>;
}
