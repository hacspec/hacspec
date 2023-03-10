use hacspec_lib::*;
use crate::types::*;
use crate::env::*;
use libcrux::hpke::aead::AEAD::*;
use libcrux::hpke::kdf::KDF::*;
use libcrux::hpke::kem::KEM::*;
use libcrux::hpke::{Mode::*, *};

// This is a partial implementation of a crypto API
// All functions should connect to libcrux

pub fn pke_encrypt(pk_b:Pubkey,m:Bytes,env:&mut Env) -> Bytes {
    let config = HPKEConfig(
        mode_base,
        DHKEM_X25519_HKDF_SHA256,
        HKDF_SHA256,
        ChaCha20Poly1305,
    );
    
    let pk_r = Bytes::from_seq(&pk_b);
    let info = Bytes::new(0);
    let aad = Bytes::new(0);
    
    let randomness = rand_gen(64,env);

    let HPKECiphertext(enc, ct) = HpkeSeal(
        config, &pk_r, &info, &aad, &m, None, None, None, randomness,
    )
    .expect("Error in hpke seal");
    let mut res = Bytes::new(4);
    let enclen = enc.len();
    res[0] = enclen as u8;
    res[1] = (enclen >> 8) as u8;
    res[2] = (enclen >> 16) as u8;
    res[3] = (enclen >> 24) as u8;
    res.concat(&enc).concat(&ct)
}

// TODO: Use HPKE decrypt
pub fn pke_decrypt(sk_b:Privkey,m:Bytes,env:&mut Env) -> Option<Bytes> {
    if m.len() < 4 {None}
    else {
        let (lenb,rest) = m.split_off(4);
        let lena = [lenb[0],lenb[1],lenb[2],lenb[3]];
        let len = u32::from_le_bytes(lena);
        let (enc,ct) = rest.split_off(len as usize);
        let config = HPKEConfig(
            mode_base,
            DHKEM_X25519_HKDF_SHA256,
            HKDF_SHA256,
            ChaCha20Poly1305,
        );
    
    
        let info = Bytes::new(0);
        let aad = Bytes::new(0);
        let sk_r = Bytes::from_seq(&sk_b);

        let decrypted_ptxt = HpkeOpen(
            config,
            &HPKECiphertext(enc,ct),
            &sk_r,
            &info,
            &aad,
            None,
            None,
            None,
        );
        match decrypted_ptxt {
            Ok(p) => Some(p),
            _ => None
        }
    }
}