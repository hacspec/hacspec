// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Import chacha20 and poly1305
use hacspec_chacha20::*;
use hacspec_poly1305::*;

fn pad_aad_msg(aad: &ByteSeq, msg: &ByteSeq) -> ByteSeq {
    let laad = aad.len();
    let lmsg = msg.len();
    let mut pad_aad = 16 * ((laad >> 4u32) + 1);
    let mut pad_msg = 16 * ((lmsg >> 4u32) + 1);
    if laad % 16 == 0 {
        pad_aad = laad;
        pad_msg = lmsg;
    };
    let mut padded_msg = ByteSeq::new(pad_aad + pad_msg + 16);
    padded_msg = padded_msg.update(0, aad);
    padded_msg = padded_msg.update(pad_aad, msg);
    padded_msg = padded_msg.update(pad_aad + pad_msg, &U64_to_le_bytes(U64(laad as u64)));
    padded_msg = padded_msg.update(pad_aad + pad_msg + 8, &U64_to_le_bytes(U64(lmsg as u64)));
    padded_msg
}

pub fn encrypt(key: Key, iv: IV, aad: &ByteSeq, msg: &ByteSeq) -> (ByteSeq, Tag) {
    let key_block = block(key, U32(0u32), iv);
    let mac_key = Key::from_slice_range(&key_block, 0..32);
    let cipher_text = chacha(key, iv, msg);
    let padded_msg = pad_aad_msg(aad, &cipher_text);
    let tag = poly(&padded_msg, mac_key);
    (cipher_text, tag)
}

pub fn decrypt(
    key: Key,
    iv: IV,
    aad: &ByteSeq,
    cipher_text: &ByteSeq,
    tag: Tag,
) -> (ByteSeq, bool) {
    let key_block = block(key, U32(0u32), iv);
    let mac_key = Key::from_slice_range(&key_block, 0..32);
    let padded_msg = pad_aad_msg(aad, cipher_text);
    let my_tag = poly(&padded_msg, mac_key);
    let plain_text = chacha(key, iv, cipher_text);
    (plain_text, my_tag == tag)
}
