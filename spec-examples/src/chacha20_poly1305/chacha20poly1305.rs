// Import hacspec and all needed definitions.
use hacspec::prelude::*;

// Import chacha20 and poly1305
use super::chacha20::*;
use super::poly1305::*;

fn pad_aad_msg(aad: ByteSeq, msg: ByteSeq) -> ByteSeq {
    let laad = aad.len();
    let lmsg = msg.len();
    let pad_aad = if laad % 16 == 0 {
        laad
    } else {
        16 * ((laad >> 4) + 1)
    };
    let pad_msg = if lmsg % 16 == 0 {
        lmsg
    } else {
        16 * ((lmsg >> 4) + 1)
    };
    let mut padded_msg = ByteSeq::new(pad_aad + pad_msg + 16);
    padded_msg = padded_msg.update(0, aad);
    padded_msg = padded_msg.update(pad_aad, msg);
    padded_msg = padded_msg.update(pad_aad + pad_msg, u64_to_le_bytes(U64(laad as u64)));
    padded_msg = padded_msg.update(pad_aad + pad_msg + 8, u64_to_le_bytes(U64(lmsg as u64)));
    padded_msg
}

pub fn encrypt(key: Key, iv: IV, aad: ByteSeq, msg: ByteSeq) -> Result<(ByteSeq, Tag), String> {
    let key_block = block(key, U32(0), iv);
    let mac_key = Key::from_sub(key_block, 0..32);
    let cipher_text = match chacha(key, iv, msg) {
        Ok(c) => c,
        Err(r) => {
            println!("Error encrypting chacha20: {}", r);
            return Err(r);
        }
    };
    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let tag = poly(padded_msg, mac_key);
    Ok((cipher_text, tag))
}

pub fn decrypt(
    key: Key,
    iv: IV,
    aad: ByteSeq,
    cipher_text: ByteSeq,
    tag: Tag,
) -> Result<ByteSeq, String> {
    let key_block = block(key, U32(0), iv);
    let mac_key = Key::from_sub(key_block, 0..32);
    let padded_msg = pad_aad_msg(aad, cipher_text.clone());
    let my_tag = poly(padded_msg, mac_key);
    if my_tag == tag {
        match chacha(key, iv, cipher_text) {
            Ok(c) => Ok(c),
            Err(r) => {
                println!("Error decrypting chacha20: {}", r);
                Err(r)
            }
        }
    } else {
        Err("Mac verification failed".to_string())
    }
}
