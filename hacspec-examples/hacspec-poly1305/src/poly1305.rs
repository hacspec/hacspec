// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Import chacha20
use hacspec_chacha20::*;

const BLOCKSIZE: usize = 16;
// Type definitions for use in poly1305.

// These are type aliases for convenience
bytes!(Block, BLOCKSIZE);

// These are actual types; fixed-length arrays.
public_bytes!(Tag, BLOCKSIZE);

public_nat_mod!(
    FieldElement,
    FieldCanvas,
    272,
    "03fffffffffffffffffffffffffffffffb"
);

fn key_gen(key: Key, iv: IV) -> Key {
    let block = block(key, U32(0u32), iv);
    Key::from_slice_range(&block, 0..32)
}

fn encode_r(r: Block) -> FieldElement {
    let r_128 = U128Word::from_slice(&r, 0, BLOCKSIZE);
    let r_uint = U128_from_le_bytes(r_128);
    let r_uint = r_uint & U128(0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffffu128);
    FieldElement::from_secret_literal(r_uint)
}

fn encode(block: &ByteSeq) -> FieldElement {
    let block_len = block.len();
    let block_as_u128 = U128Word::from_slice(block, 0, min(16, block_len));
    let w_elem = FieldElement::from_secret_literal(U128_from_le_bytes(block_as_u128));
    let l_elem = FieldElement::from_canvas(FieldCanvas::pow2(8 * block_len));
    w_elem + l_elem
}

fn poly_inner(m: &ByteSeq, r: FieldElement) -> FieldElement {
    let mut acc = FieldElement::from_literal(0u128);
    for i in 0..m.num_chunks(BLOCKSIZE) {
        let (_, block) = m.get_chunk(BLOCKSIZE, i);
        acc = (acc + encode(&block)) * r;
    }
    acc
}

pub fn poly(m: &ByteSeq, key: Key) -> Tag {
    let s_elem = FieldElement::from_secret_literal(U128_from_le_bytes(U128Word::from_slice(
        &key, BLOCKSIZE, BLOCKSIZE,
    )));
    let r_elem = encode_r(Block::from_slice_range(&key, 0..BLOCKSIZE));
    let a = poly_inner(m, r_elem);
    let n = a + s_elem;
    // Note that n might be less than 16 byte -> zero-pad; but might also be
    // larger than Tag::capacity().
    let n_v = n.to_public_byte_seq_le();
    let mut tag = Tag::new();
    for i in 0..min(tag.len(), n_v.len()) {
        tag[i] = n_v[i];
    }
    tag
}

pub fn poly_mac(m: &ByteSeq, key: Key, iv: IV) -> Tag {
    let mac_key = key_gen(key, iv);
    poly(m, mac_key)
}
