// Import hacspec and all needed definitions.
use hacspec::prelude::*;

// Import aes and gcm
use super::aes::{
    self, aes128_ctr_keyblock, aes128_decrypt, aes128_encrypt, aes256_ctr_keyblock, aes256_decrypt,
    aes256_encrypt, Block,
};

use super::gf128::{gmac, Key, Tag};

fn pad_aad_msg(aad: ByteSeq, msg: ByteSeq) -> ByteSeq {
    let laad = aad.len();
    let lmsg = msg.len();
    let pad_aad = if laad % 16 == 0 {
        laad
    } else {
        laad + (16 - (laad % 16))
    };
    let pad_msg = if lmsg % 16 == 0 {
        lmsg
    } else {
        lmsg + (16 - (lmsg % 16))
    };
    let mut padded_msg = ByteSeq::new(pad_aad + pad_msg + 16);
    padded_msg = padded_msg.update(0, aad);
    padded_msg = padded_msg.update(pad_aad, msg);
    padded_msg = padded_msg.update(
        pad_aad + pad_msg,
        U64_to_be_bytes(U64(laad as u64) * U64(8)),
    );
    padded_msg = padded_msg.update(
        pad_aad + pad_msg + 8,
        U64_to_be_bytes(U64(lmsg as u64) * U64(8)),
    );
    padded_msg
}

pub fn encrypt_aes128(
    key: aes::Key128,
    iv: aes::Nonce,
    aad: ByteSeq,
    msg: ByteSeq,
) -> (ByteSeq, Tag) {
    let iv0 = aes::Nonce::new();

    let mac_key = aes128_ctr_keyblock(key, iv0, U32(0), 4, 10);
    let tag_mix = aes128_ctr_keyblock(key, iv, U32(1), 4, 10);

    let cipher_text = aes128_encrypt(key, iv, U32(2), msg);
    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let tag = gmac(padded_msg, Key::from_seq(mac_key));
    let tag = aes::xor_block(Block::from_seq(tag), tag_mix);

    (cipher_text, Tag::from_seq(tag))
}

pub fn encrypt_aes256(
    key: aes::Key256,
    iv: aes::Nonce,
    aad: ByteSeq,
    msg: ByteSeq,
) -> (ByteSeq, Tag) {
    let iv0 = aes::Nonce::new();

    let mac_key = aes256_ctr_keyblock(key, iv0, U32(0), 8, 14);
    let tag_mix = aes256_ctr_keyblock(key, iv, U32(1), 8, 14);

    let cipher_text = aes256_encrypt(key, iv, U32(2), msg);
    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let tag = gmac(padded_msg, Key::from_seq(mac_key));
    let tag = aes::xor_block(Block::from_seq(tag), tag_mix);

    (cipher_text, Tag::from_seq(tag))
}

pub fn decrypt_aes128(
    key: aes::Key128,
    iv: aes::Nonce,
    aad: ByteSeq,
    cipher_text: ByteSeq,
    tag: Tag,
) -> Result<ByteSeq, String> {
    let iv0 = aes::Nonce::new();

    let mac_key = aes128_ctr_keyblock(key, iv0, U32(0), 4, 10);
    let tag_mix = aes128_ctr_keyblock(key, iv, U32(1), 4, 10);

    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let my_tag = gmac(padded_msg, Key::from_seq(mac_key));
    let my_tag = aes::xor_block(Block::from_seq(my_tag), tag_mix);

    if my_tag.declassify_eq(Block::from_seq(tag)) {
        Ok(aes128_decrypt(key, iv, U32(2), cipher_text))
    } else {
        Err("Mac verification failed".to_string())
    }
}

pub fn decrypt_aes256(
    key: aes::Key256,
    iv: aes::Nonce,
    aad: ByteSeq,
    cipher_text: ByteSeq,
    tag: Tag,
) -> Result<ByteSeq, String> {
    let iv0 = aes::Nonce::new();

    let mac_key = aes256_ctr_keyblock(key, iv0, U32(0), 8, 14);
    let tag_mix = aes256_ctr_keyblock(key, iv, U32(1), 8, 14);

    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let my_tag = gmac(padded_msg, Key::from_seq(mac_key));
    let my_tag = aes::xor_block(Block::from_seq(my_tag), tag_mix);

    if my_tag.declassify_eq(Block::from_seq(tag)) {
        Ok(aes256_decrypt(key, iv, U32(2), cipher_text))
    } else {
        Err("Mac verification failed".to_string())
    }
}
