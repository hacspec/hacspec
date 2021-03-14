// A module that wraps all the Generic crypto needed by TLS 1.3
// Each function below should be supported by a standard crypto library

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub type Res<T> = Result<T, usize>;
pub type Bytes = Seq<U8>;
pub fn empty() -> Bytes {
    return Seq::new(0);
}

pub fn bytes<T: SeqTrait<U8>>(x: &T) -> Bytes {
    return Seq::from_seq(x);
}

bytes!(Entropy, 64);
bytes!(Random, 32);

pub type DHSK = Bytes; 
pub type DHPK = Bytes;
pub type SIGK = Bytes; 
pub type VERK = Bytes;
pub type MACK = Bytes;
pub type AEK = Bytes;
pub type KEY = Bytes;
pub type HASH = Bytes;
pub type HMAC = Bytes;
pub type SIG = Bytes;
pub type AEIV = Bytes;

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

pub fn hash_len(ha:HashAlgorithm) -> u16 {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48
    }
}

pub fn hmac_key_len(ha:HashAlgorithm) -> u16 {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48
    }
}
pub fn ae_key_len(ae:AEADAlgorithm) -> u16 {
    match ae {
        AEADAlgorithm::CHACHA20_POLY1305 => 32,
        AEADAlgorithm::AES_128_GCM => 32,
        AEADAlgorithm::AES_256_GCM => 32
    }
}

pub fn ae_iv_len(ae:AEADAlgorithm) -> u16 {
    match ae {
        AEADAlgorithm::CHACHA20_POLY1305 => 12,
        AEADAlgorithm::AES_128_GCM => 12,
        AEADAlgorithm::AES_256_GCM => 12
    }
}

pub fn dh_priv_len(gn:NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::SECP256r1 => 32
    }
}

pub fn dh_pub_len(gn:NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::SECP256r1 => 64
    }
}

pub fn zero_key(ha:HashAlgorithm) -> KEY {
    KEY::new(hash_len(ha) as usize)
} 

pub fn secret_to_public(group_name: NamedGroup, x: &DHSK) -> Res<DHPK> {
    return Ok(DHPK::new(32));
}

pub fn ecdh(group_name: NamedGroup, x: &DHSK, y: &DHPK) -> Res<KEY> {
    return Ok(KEY::new(32));
}

pub fn hash(ha: HashAlgorithm, payload: &Bytes) -> Res<HASH> {
    return Ok(HASH::new(32));
}

pub fn hmac(ha: HashAlgorithm, mk: &MACK, payload: &Bytes) -> Res<HMAC> {
    return Ok(HMAC::new(32));
}

pub fn hmac_verify(ha: HashAlgorithm, mk: &MACK, payload: &Bytes, m: &HMAC) -> Res<()> {
    return Ok(());
}

pub fn sign(sa: SignatureScheme, ps: &SIGK, payload: &Bytes) -> Res<SIG> {
    return Ok(SIG::new(32));
}
pub fn verify(sa: SignatureScheme, pk: &VERK, payload: &Bytes, sig: &Bytes) -> Res<()> {
    return Ok(());
}

pub fn hkdf_extract(ha: HashAlgorithm, k: &KEY, salt: &KEY) -> Res<KEY> {
    return Ok(KEY::new(32));
}

pub fn hkdf_expand(ha: HashAlgorithm, k: &KEY, info: &Bytes, len: usize) -> Res<KEY> {
    return Ok(KEY::new(32));
}

pub fn aead_encrypt(a: AEADAlgorithm, k: &AEK, iv: &AEIV, payload: &Bytes, ad: &Bytes) -> Res<Bytes> {
    return Ok(empty());
}

pub fn aead_decrypt(a: AEADAlgorithm, k: &AEK, iv: &AEIV, Ciphertext: &Bytes, ad: &Bytes) -> Res<Bytes> {
    return Ok(empty());
}
