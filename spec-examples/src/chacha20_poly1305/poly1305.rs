// Import hacspec and all needed definitions.
use hacspec::prelude::*;

// Import chacha20
use super::chacha20::{self, *};

const BLOCKSIZE: usize = 16;
// Type definitions for use in poly1305.

// These are type aliases for convenience
bytes!(Block, BLOCKSIZE);

// These are actual types; fixed-length arrays.
bytes!(Tag, BLOCKSIZE);

public_nat_mod!(FieldElement, FieldCanvas, 272, "03fffffffffffffffffffffffffffffffb");

fn key_gen(key: Key, iv: IV) -> Key {
    let block = chacha20::block(key, U32(0), iv);
    Key::from_sub(block, 0..32)
}

fn encode_r(r: Block) -> FieldElement {
    let mut r_128 = U128Word::new();
    r_128 = r_128.update_sub(0, r, 0, BLOCKSIZE);
    let r_uint = u128_from_le_bytes(r_128);
    let r_uint = r_uint & U128(0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffff);
    FieldElement::from_secret_literal(r_uint)
}

fn encode(block: ByteSeq) -> FieldElement {
    let mut block_as_u128 = U128Word::new();
    let block_len = block.len();
    block_as_u128 = block_as_u128.update_sub(0, block, 0, min(16, block_len));
    let w_elem = FieldElement::from_secret_literal(u128_from_le_bytes(block_as_u128));
    let l_elem = FieldCanvas::pow2(8 * block_len).into();
    w_elem + l_elem
}

fn poly_inner(m: ByteSeq, r: FieldElement) -> FieldElement {
    let mut acc = FieldElement::from_literal(0);
    let m_len = m.len();
    for i in (0..m_len).step_by(BLOCKSIZE) {
        let block_len = min(BLOCKSIZE, m_len - i);
        let mut b = Seq::new(block_len);
        b = b.update_sub(0, m.clone(), i, block_len);
        acc = (acc + encode(b)) * r;
    }
    acc
}

pub fn poly(m: ByteSeq, key: Key) -> Tag {
    let s_elem = FieldElement::from_secret_literal(u128_from_le_bytes(U128Word::from_sub(
        key,
        BLOCKSIZE..2 * BLOCKSIZE,
    )));
    let r_elem = encode_r(Block::from_sub(key, 0..BLOCKSIZE));
    let a = poly_inner(m, r_elem);
    let n = a + s_elem;
    // Note that n might be less than 16 byte -> zero-pad; but might also be
    // larger than Tag::capacity().
    let n_v = n.to_byte_seq_le();
    let mut tag = Tag::new();
    for i in 0..min(tag.len(), n_v.len()) {
        tag[i] = n_v[i];
    }
    tag
}

pub fn poly_mac(m: ByteSeq, key: Key, iv: IV) -> Tag {
    let mac_key = key_gen(key, iv);
    poly(m, mac_key)
}
