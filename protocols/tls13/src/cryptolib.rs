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
use hacspec_ecdsa_p256_sha256::*;
use hacspec_hkdf::*;
use hacspec_hmac::hmac as hacspec_hmac;
use hacspec_p256::*;
use hacspec_poly1305::Tag as Poly1305Tag;
use unsafe_hacspec_examples::aes_gcm::{
    aes::{Key128, Key256, Nonce as AesNonce},
    decrypt_aes128, encrypt_aes128,
    gf128::Tag as GcmTag,
};

use crate::{
    crypto_error, hkdf_error, insufficient_entropy, invalid_cert, mac_failed,
    unsupported_algorithm, verify_failed,
};

use backtrace::Backtrace;
pub type Res<T> = Result<T, usize>;
pub fn err<T>(x: usize) -> Res<T> {
    let bt = Backtrace::new();
    println!("{:?}", bt);
    Err(x)
}

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

pub type Entropy = Bytes;
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

#[derive(Clone, Copy, PartialEq, Debug)]
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
        AEADAlgorithm::AES_128_GCM => 16,
        AEADAlgorithm::AES_256_GCM => 16,
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
            let (success, (X, Y)) = p256_point_mul_base(P256Scalar::from_byte_seq_be(x));
            if success {
                Ok(X.to_byte_seq_be().concat(&Y.to_byte_seq_be()))
            } else {
                Err(crypto_error)
            }
        }
        NamedGroup::X25519 => Ok(DHPK::from_seq(&x25519_secret_to_public(
            SerializedScalar::from_seq(x),
        ))),
    }
}

pub fn ecdh(group_name: &NamedGroup, x: &DHSK, y: &DHPK) -> Res<KEY> {
    match group_name {
        NamedGroup::SECP256r1 => {
            let pk = (
                P256FieldElement::from_byte_seq_be(&y.slice_range(0..32)),
                P256FieldElement::from_byte_seq_be(&y.slice_range(32..64)),
            );
            let (success, (X, Y)) = p256_point_mul(P256Scalar::from_byte_seq_be(x), pk);
            if success {
                Ok(X.to_byte_seq_be().concat(&Y.to_byte_seq_be()))
            } else {
                Err(crypto_error)
            }
        }
        NamedGroup::X25519 => Ok(DHPK::from_seq(&x25519_point_mul(
            SerializedScalar::from_seq(x),
            SerializedPoint::from_seq(y),
        ))),
    }
}

pub type KEMScheme = NamedGroup;
pub type KEMSK = Bytes;
pub type KEMPK = Bytes;

pub fn kem_priv_len(ks: &KEMScheme) -> usize {
    dh_priv_len(ks)
}

pub fn kem_pub_len(ks: &KEMScheme) -> usize {
    dh_pub_len(ks)
}

pub fn kem_priv_to_pub(ks: &KEMScheme, sk: &KEMSK) -> Res<KEMPK> {
    secret_to_public(ks, sk)
}

pub fn kem_keygen(ks: &KEMScheme, ent: Entropy) -> Res<(KEMSK, KEMPK)> {
    if ent.len() < dh_priv_len(ks) {
        Err(insufficient_entropy)
    } else {
        let sk = KEMSK::from_seq(&ent.slice_range(0..dh_priv_len(ks)));
        let pk = kem_priv_to_pub(ks, &sk)?;
        Ok((sk, pk))
    }
}

pub fn kem_encap(ks: &KEMScheme, pk: &KEMPK, ent: Entropy) -> Res<(KEY, Bytes)> {
    let (x, gx) = kem_keygen(ks, ent)?;
    let gxy = ecdh(ks, &x, pk)?;
    Ok((gxy, gx))
}

pub fn kem_decap(ks: &KEMScheme, ct: &Bytes, sk: KEMSK) -> Res<KEY> {
    let gxy = ecdh(ks, &sk, &ct)?;
    Ok(gxy)
}

pub fn hash(ha: &HashAlgorithm, payload: &Bytes) -> Res<HASH> {
    match ha {
        HashAlgorithm::SHA256 => Ok(HASH::from_seq(&sha256(payload))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn hmac(ha: &HashAlgorithm, mk: &MACK, payload: &Bytes) -> Res<HMAC> {
    match ha {
        HashAlgorithm::SHA256 => Ok(HMAC::from_seq(&hacspec_hmac(mk, payload))),
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
    // cert is an ASN.1 sequence. Take the first sequence inside the outer.
    // Skip 1 + length bytes
    fn get_length_length(b: &Bytes) -> usize {
        if U8::declassify(b[0]) >> 7 == 1 {
            declassify_usize_from_U8(b[0] & U8(0x7fu8))
        } else {
            0
        }
    }
    fn get_length(b: &Bytes, len: usize) -> usize {
        declassify_u32_from_U32(U32_from_be_bytes(U32Word::from_slice(b, 0, len))) as usize
            >> ((4 - len) * 8)
    }
    fn get_short_length(b: &Bytes) -> usize {
        declassify_usize_from_U8(b[0] & U8(0x7fu8))
    }
    let skip = 2 + get_length_length(&cert.slice_range(1..cert.len())) + 1;
    let seq1_len_len = get_length_length(&cert.slice_range(skip..cert.len()));
    let skip = skip + 1;
    let seq1_len = get_length(&cert.slice(skip, cert.len() - skip), seq1_len_len);
    let mut seq1 = cert.slice_range(skip + seq1_len_len..skip + seq1_len_len + seq1_len);

    // Read sequences until we find the ecPublicKey (we don't support anything else right now)
    let mut pk = VERK::new(0);
    while skip < seq1.len() && pk.len() == 0 {
        let element_type = U8::declassify(seq1[0]);
        seq1 = seq1.slice(1, seq1.len() - 1);
        let len_len = get_length_length(&seq1);
        let mut len = get_short_length(&seq1);
        seq1 = seq1.slice(1, seq1.len() - 1);
        if len_len != 0 {
            len = get_length(&seq1, len_len);
        }
        if element_type == 0x30 {
            // peek into this sequence to see if sequence again with an ecPublicKey
            // as first element
            let seq2 = seq1.slice(len_len, len);
            let element_type = U8::declassify(seq2[0]);
            let seq2 = seq2.slice(1, seq2.len() - 1);
            if element_type == 0x30 {
                let len_len = get_length_length(&seq2);
                if len_len == 0 {
                    let oid_len = get_short_length(&seq2);
                    if oid_len >= 9 {
                        // ecPublicKey oid incl tag: 06 07 2A 86 48 CE 3D 02 01
                        let oid = seq2.slice(1, 9);
                        if oid
                            == Bytes::from_public_slice(&[
                                0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01,
                            ])
                        {
                            // We have an ecPublicKey, skip the inner sequences
                            // and read the public key from the bit string
                            let bit_string = seq2.slice(oid_len + 1, seq2.len() - oid_len - 1);
                            // We only support uncompressed points
                            if U8::declassify(bit_string[0]) == 0x03 {
                                let pk_len = declassify_usize_from_U8(bit_string[1]); // 42
                                let _zeroes = declassify_usize_from_U8(bit_string[2]); // 00
                                let _uncompressed = declassify_usize_from_U8(bit_string[3]); // 04
                                pk = bit_string.slice(4, pk_len - 2);
                            }
                        }
                    }
                }
            }
        }
        seq1 = seq1.slice(len, seq1.len() - len);
    }
    if pk.len() == 0 {
        Err(invalid_cert)
    } else {
        Ok(pk)
    }
}

pub fn sign(sa: &SignatureScheme, ps: &SIGK, payload: &Bytes, ent: Entropy) -> Res<SIG> {
    match sa {
        SignatureScheme::ECDSA_SECP256r1_SHA256 => {
            let random = Random::from_seq(&ent.slice_range(0..32));
            // FIXME: we must do rejection sampling here.
            let nonce = P256Scalar::from_byte_seq_be(&random);
            let (success, (r, s)) =
                ecdsa_p256_sha256_sign(payload, P256Scalar::from_byte_seq_be(ps), nonce);
            if success {
                let signature = SIG::new(0)
                    .concat(&r.to_byte_seq_be())
                    .concat(&s.to_byte_seq_be());
                Ok(signature)
            } else {
                Err(crypto_error)
            }
        }
        _ => Err(unsupported_algorithm),
    }
}
pub fn verify(sa: &SignatureScheme, pk: &VERK, payload: &Bytes, sig: &Bytes) -> Res<()> {
    println!("sa: {:?}", sa);
    println!("sig: {:?}", sig);
    println!("pk: {:x?}", pk);
    println!("payload: {:x?}", payload);
    match sa {
        SignatureScheme::ECDSA_SECP256r1_SHA256 => {
            let (pk_x, pk_y) = (
                P256FieldElement::from_byte_seq_be(&pk.slice(0, 32)),
                P256FieldElement::from_byte_seq_be(&pk.slice(32, 32)),
            );
            let (r, s) = (
                P256Scalar::from_byte_seq_be(&sig.slice(0, 32)),
                P256Scalar::from_byte_seq_be(&sig.slice(32, 32)),
            );
            if ecdsa_p256_sha256_verify(payload, (pk_x, pk_y), (r, s)) {
                Ok(())
            } else {
                println!("Invalid signature");
                Err(verify_failed)
            }
        }
        _ => Err(unsupported_algorithm),
    }
}

pub fn hkdf_extract(ha: &HashAlgorithm, k: &KEY, salt: &KEY) -> Res<KEY> {
    match ha {
        HashAlgorithm::SHA256 => Ok(KEY::from_seq(&extract(salt, k))),
        HashAlgorithm::SHA384 => Err(unsupported_algorithm),
    }
}

pub fn hkdf_expand(ha: &HashAlgorithm, k: &KEY, info: &Bytes, len: usize) -> Res<KEY> {
    match ha {
        HashAlgorithm::SHA256 => {
            let (success, bytes) = expand(k, info, len);
            if success {
                Ok(KEY::from_seq(&bytes))
            } else {
                Err(hkdf_error)
            }
        }
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