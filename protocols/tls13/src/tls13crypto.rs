// A module that wraps all the Generic crypto needed by TLS 1.3
// Each function below should be supported by a standard crypto library
use crate::tls13formats::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

bytes!(Entropy, 64);
bytes!(Random, 32);
bytes!(DHSK, 32);
bytes!(DHPK, 32);
bytes!(SIGK, 32);
bytes!(VERK, 32);
bytes!(MACK, 32);
bytes!(AEK, 32);
bytes!(KEY, 32);
bytes!(HASH, 32);
bytes!(HMAC, 32);
bytes!(SIG, 64);
bytes!(AEIV, 12);

pub const zeros : KEY = KEY(secret_bytes!([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]));

pub type AEKIV = (AEK,AEIV);

#[derive(Clone, Copy, PartialEq)]
pub enum NamedGroup {
    X25519,
    SECP256r1,
}

#[derive(Clone, Copy, PartialEq)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
}

#[derive(Clone, Copy, PartialEq)]
pub enum AEADAlgorithm {
    CHACHA20_POLY1305,
    AES_128_GCM,
    AES_256_GCM,
}

#[derive(Clone, Copy, PartialEq)]
pub enum SignatureScheme {
    ED25519,
    ECDSA_SECP256r1_SHA256,
    RSA_PSS_RSAE_SHA256,
}

//pub type DH_KEYPAIR = (NamedGroup, DHSK, DHPK);
pub type PSK = KEY;

pub fn secret_to_public(group_name: NamedGroup, x: DHSK) -> Res<DHPK> {
    return Ok(DHPK::new());
}

pub fn ecdh(group_name: NamedGroup, x: DHSK, y: DHPK) -> Res<KEY> {
    return Ok(KEY::new());
}

pub fn hmac(ha: HashAlgorithm, mk: MACK, payload: &Bytes) -> Res<HMAC> {
    return Ok(HMAC::new());
}

pub fn hmac_verify(ha: HashAlgorithm, mk: MACK, payload: &Bytes, m: HMAC) -> Res<()> {
    return Ok(());
}

pub fn sign(sa: SignatureScheme, ps: SIGK, payload: &Bytes) -> Res<SIG> {
    return Ok(SIG::new());
}
pub fn verify(sa: SignatureScheme, pk: VERK, payload: &Bytes, sig: Bytes) -> Res<()> {
    return Ok(());
}

pub fn hkdf_extract(ha: HashAlgorithm, k: KEY, salt: KEY) -> Res<KEY> {
    return Ok(k);
}

pub fn hkdf_expand(ha: HashAlgorithm, k: KEY, info: Bytes, len: usize) -> Res<KEY> {
    return Ok(k);
}

pub fn aead_encrypt(a: AEADAlgorithm, k: AEK, iv: AEIV, payload: Bytes, ad: Bytes) -> Res<Bytes> {
    return Ok(payload);
}

pub fn aead_decrypt(a: AEADAlgorithm, k: AEK, iv: AEIV, Ciphertext: Bytes, ad: Bytes) -> Res<Bytes> {
    return Ok(Ciphertext);
}

pub fn hash_empty(ha:HashAlgorithm) -> HASH {
    return (HASH::new());
}