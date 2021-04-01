// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Import chacha20 and poly1305
use hacspec_chacha20::*;
use hacspec_poly1305::*;

pub type ChaChaPolyKey = ChaChaKey;
pub type ChaChaPolyIV = ChaChaIV;

pub fn init(key: ChaChaPolyKey, iv: ChaChaPolyIV) -> PolyState {
    let key_block0 = chacha20_key_block0(key, iv);
    let poly_key = PolyKey::from_slice(&key_block0,0,32);
    poly1305_init(poly_key)
}

pub fn update_padded (m:&ByteSeq, st:PolyState) -> PolyState {
    let mut st = st;
    for i in 0..m.num_chunks(16) {
        let (_, block) = m.get_chunk(16, i);
        st = poly1305_update1(16,&block,st); // This is the only line that changes from poly1305_update.
                                             // And then again it only makes a difference for poly1305_update_last
    }
    st
}

pub fn finish(aadlen:usize, cipherlen:usize, st:PolyState) -> Tag {
    let mut last_block = PolyBlock::new();
    last_block = last_block.update(0,&U64_to_le_bytes(U64(aadlen as u64)));
    last_block = last_block.update(8,&U64_to_le_bytes(U64(cipherlen as u64)));
    let st = poly1305_update1(16,&SubBlock::from_seq(&last_block),st);
    poly1305_finish(st)
}

pub fn encrypt(key: ChaChaPolyKey, iv: ChaChaPolyIV, aad: &ByteSeq, msg: &ByteSeq) -> (ByteSeq, Tag) {
    let cipher_text = chacha20(key, iv, 1u32, msg);
    let mut poly_st = init(key,iv);
    poly_st = update_padded(aad, poly_st);
    poly_st = update_padded(&cipher_text, poly_st);
    let tag = finish(aad.len(),cipher_text.len(),poly_st);
    (cipher_text, tag)
}


pub fn decrypt(key: ChaChaPolyKey, iv: ChaChaPolyIV, aad: &ByteSeq, cipher_text: &ByteSeq, tag: Tag) ->
       Option<ByteSeq> {
    let mut poly_st = init(key,iv);
    poly_st = update_padded(aad, poly_st);
    poly_st = update_padded(cipher_text, poly_st);
    let my_tag = finish(aad.len(),cipher_text.len(),poly_st);
    if my_tag.declassify_eq(&tag) {
        Some(chacha20(key, iv, 1u32, cipher_text))
    } else {None}
}
