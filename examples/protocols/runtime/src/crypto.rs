use hacspec_lib::*;
use crate::types::*;
use crate::env::*;
use tls_cryptolib::*;

// This is a dummy implementation of a Crypto Interface.
// Replace with libcrux

// TODO: Use HPKE encrypt
pub fn pke_encrypt(pk_b:Pubkey,m:Bytes,env:&mut Env) -> Bytes {
    Seq::new(32)
}

// TODO: Use HPKE decrypt
pub fn pke_decrypt(sk_b:Privkey,m:Bytes,env:&mut Env) -> Option<Bytes> {
    None
}