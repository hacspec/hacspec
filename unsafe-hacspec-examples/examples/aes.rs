#![allow(dead_code)]

use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use unsafe_hacspec_examples::aes_gcm::aes::*;

fn read_file() -> Vec<u8> {
    let mut file = File::open("input.data").unwrap();
    let mut data = Vec::new();
    let _read = file.read_to_end(&mut data);
    data
}

fn aes_128_enc_dec(m: &ByteSeq, key: Key128, iv: Nonce, ctr: U32, ctxt: Option<&ByteSeq>) {
    let c = aes128_encrypt(key, iv, ctr, m);
    let m_dec = aes128_decrypt(key, iv, ctr, &c);
    assert_bytes_eq!(m, m_dec);
    if ctxt.is_some() {
        assert_bytes_eq!(c, ctxt.unwrap());
    }
}

fn aes_256_enc_dec(m: &ByteSeq, key: Key256, iv: Nonce, ctr: U32, ctxt: Option<&ByteSeq>) {
    let c = aes256_encrypt(key, iv, ctr, m);
    let m_dec = aes256_decrypt(key, iv, ctr, &c);
    assert_bytes_eq!(m, m_dec);
    if ctxt.is_some() {
        assert_bytes_eq!(c, ctxt.unwrap());
    }
}

fn main() {
    let data = ByteSeq::from_public_slice(&read_file());
    let key = Key128::from_public_slice(&[
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f,
        0x3c,
    ]);
    let nonce = Nonce::from_public_slice(&[
        0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
    ]);
    aes_128_enc_dec(&data, key, nonce, U32(0), None);
}
