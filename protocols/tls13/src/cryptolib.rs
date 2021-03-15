// A module that wraps all the Generic crypto needed by TLS 1.3
// Each function below should be supported by a standard crypto library

// Import hacspec and all needed definitions.
use hacspec_lib::*;

use hacspec_sha256::*;
// XXX: this type of import is not allowed in hacspec
use hacspec_chacha20::{Key as Chacha20Key, IV as Chacha20Iv};
use hacspec_chacha20poly1305::{decrypt as chacha_poly_decrypt, encrypt as chacha_poly_encrypt};
use hacspec_curve25519::{
    scalarmult as x25519_point_mul, secret_to_public as x25519_secret_to_public, SerializedPoint,
    SerializedScalar,
};
use hacspec_poly1305::Tag as Poly1305Tag;
use unsafe_hacspec_examples::{
    aes_gcm::{
        aes::{Key128, Key256, Nonce as AesNonce},
        decrypt_aes128, encrypt_aes128,
        gf128::Tag as GcmTag,
    },
    ec::{
        p256::{
            point_mul as p256_point_mul, point_mul_base as p256_secret_to_public,
            FieldElement as P256FieldElement, Scalar as P256Scalar,
        },
        Affine,
    },
    hkdf, hmac,
};

use crate::{mac_failed, unsupported_algorithm};

pub type Res<T> = Result<T, usize>;
pub type Bytes = ByteSeq;
pub fn empty() -> Bytes {
    return Seq::new(0);
}

pub fn zeros(u: usize) -> Bytes {
    return Seq::new(u);
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

pub type AEKIV = (AEK, AEIV);

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

pub fn hash_len(ha: &HashAlgorithm) -> usize {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48,
    }
}

pub fn hmac_key_len(ha: &HashAlgorithm) -> usize {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48,
    }
}
pub fn ae_key_len(ae: &AEADAlgorithm) -> usize {
    match ae {
        AEADAlgorithm::CHACHA20_POLY1305 => 32,
        AEADAlgorithm::AES_128_GCM => 32,
        AEADAlgorithm::AES_256_GCM => 32,
    }
}

pub fn ae_iv_len(ae: &AEADAlgorithm) -> usize {
    match ae {
        AEADAlgorithm::CHACHA20_POLY1305 => 12,
        AEADAlgorithm::AES_128_GCM => 12,
        AEADAlgorithm::AES_256_GCM => 12,
    }
}

pub fn dh_priv_len(gn: &NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::SECP256r1 => 32,
    }
}

pub fn dh_pub_len(gn: &NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::SECP256r1 => 64,
    }
}

pub fn zero_key(ha: &HashAlgorithm) -> KEY {
    KEY::new(hash_len(ha) as usize)
}

pub fn secret_to_public(group_name: &NamedGroup, x: &DHSK) -> Res<DHPK> {
    match group_name {
        NamedGroup::SECP256r1 => {
            let Affine(X, Y) = p256_secret_to_public(P256Scalar::from_byte_seq_be(x));
            Ok(X.to_byte_seq_be().concat(&Y.to_byte_seq_be()))
        }
        NamedGroup::X25519 => Ok(DHPK::from_seq(&x25519_secret_to_public(
            SerializedScalar::from_seq(x),
        ))),
    }
}

pub fn ecdh(group_name: &NamedGroup, x: &DHSK, y: &DHPK) -> Res<KEY> {
    match group_name {
        NamedGroup::SECP256r1 => {
            let pk = Affine(
                P256FieldElement::from_byte_seq_be(y.slice_range(0..32)),
                P256FieldElement::from_byte_seq_be(y.slice_range(32..64)),
            );
            let Affine(X, Y) = p256_point_mul(P256Scalar::from_byte_seq_be(x), pk);
            Ok(X.to_byte_seq_be().concat(&Y.to_byte_seq_be()))
        }
        NamedGroup::X25519 => Ok(DHPK::from_seq(&x25519_point_mul(
            SerializedScalar::from_seq(x),
            SerializedPoint::from_seq(y),
        ))),
    }
}

pub fn hash(ha: &HashAlgorithm, payload: &Bytes) -> Res<HASH> {
    match ha {
        HashAlgorithm::SHA256 => Ok(HASH::from_seq(&sha256(payload))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn hmac(ha: &HashAlgorithm, mk: &MACK, payload: &Bytes) -> Res<HMAC> {
    match ha {
        HashAlgorithm::SHA256 => Ok(HMAC::from_seq(&hmac::hmac(mk, payload))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn hmac_verify(ha: &HashAlgorithm, mk: &MACK, payload: &Bytes, m: &HMAC) -> Res<()> {
    // XXX: this is pretty ugly
    let my_hmac = hmac(ha, mk, payload)?;
    let mut result = if m.len() == my_hmac.len() {
        Ok(())
    } else {
        Err(mac_failed)
    };
    for i in 0..m.len() {
        if !my_hmac[i].equal(m[i]) {
            result = Err(mac_failed);
        }
    }
    result
}

pub fn verk_from_cert(cert: &Bytes) -> Res<VERK> {
    Ok(VERK::new(64))
}

pub fn sign(sa: &SignatureScheme, ps: &SIGK, payload: &Bytes) -> Res<SIG> {
    return Ok(SIG::new(32));
}
pub fn verify(sa: &SignatureScheme, pk: &VERK, payload: &Bytes, sig: &Bytes) -> Res<()> {
    return Ok(());
}

pub fn hkdf_extract(ha: &HashAlgorithm, k: &KEY, salt: &KEY) -> Res<KEY> {
    match ha {
        HashAlgorithm::SHA256 => Ok(KEY::from_seq(&hkdf::extract(salt, k))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn hkdf_expand(ha: &HashAlgorithm, k: &KEY, info: &Bytes, len: usize) -> Res<KEY> {
    match ha {
        HashAlgorithm::SHA256 => Ok(KEY::from_seq(&hkdf::expand(k, info, len))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn aead_encrypt(
    a: &AEADAlgorithm,
    k: &AEK,
    iv: &AEIV,
    payload: &Bytes,
    ad: &Bytes,
) -> Res<Bytes> {
    // XXX: the result should be Seq<u8> not Seq<U8>.
    match a {
        AEADAlgorithm::AES_128_GCM => {
            let (ctxt, tag) =
                encrypt_aes128(Key128::from_seq(k), AesNonce::from_seq(iv), ad, payload);
            Ok(ctxt.concat(&Bytes::from_seq(&tag)))
        }
        AEADAlgorithm::AES_256_GCM => Err(unsupported_algorithm),
        AEADAlgorithm::CHACHA20_POLY1305 => {
            // XXX: ctxt should really be Seq<u8> not Seq<U8>.
            let (ctxt, tag) = chacha_poly_encrypt(
                Chacha20Key::from_seq(k),
                Chacha20Iv::from_seq(iv),
                ad,
                payload,
            );
            Ok(ctxt.concat(&Bytes::from_public_seq(&tag)))
        }
    }
}

pub fn aead_decrypt(
    a: &AEADAlgorithm,
    k: &AEK,
    iv: &AEIV,
    ciphertext: &Bytes, // XXX: this should be public, i.e. Seq<u8>/PublicByteSeq
    ad: &Bytes,
) -> Res<Bytes> {
    match a {
        AEADAlgorithm::AES_128_GCM => {
            match decrypt_aes128(
                Key128::from_seq(k),
                AesNonce::from_seq(iv),
                ad,
                &ciphertext.slice_range(0..ciphertext.len() - 16),
                GcmTag::from_seq(&ciphertext.slice_range(ciphertext.len() - 16..ciphertext.len())),
            ) {
                Ok(m) => Ok(m),
                Err(_e) => return Err(mac_failed),
            }
        }
        AEADAlgorithm::AES_256_GCM => Err(unsupported_algorithm),
        AEADAlgorithm::CHACHA20_POLY1305 => {
            // XXX: ciphertext should really be Seq<u8> not Seq<U8>.
            let (ptxt, success) = chacha_poly_decrypt(
                Chacha20Key::from_seq(k),
                Chacha20Iv::from_seq(iv),
                ad,
                &ciphertext.slice_range(0..ciphertext.len() - 16),
                Poly1305Tag::from_seq(
                    &ciphertext
                        .slice_range(ciphertext.len() - 16..ciphertext.len())
                        .declassify(),
                ),
            );
            let result = if success { Ok(ptxt) } else { Err(mac_failed) };
            result
        }
    }
}
