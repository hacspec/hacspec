// Import hacspec and all needed definitions.
use hacspec_lib::*;

// WARNING:
// This spec does not provide secret independence, and treats all keys as public.
// Consequently, it should only be used as a FORMAL SPEC, NOT as a reference implementation.

// Type definitions for use in poly1305.
bytes!(PolyKey, 32);

const BLOCKSIZE: usize = 16;

// These are type aliases for convenience
bytes!(PolyBlock, 16);

// These are actual types; fixed-length arrays.
bytes!(Tag, 16);

// A byte sequence of length <= BLOCKSIZE
pub type SubBlock = ByteSeq;

// A length <= BLOCKSIZE
pub type BlockIndex = usize;

// This defines the field for modulo 2^130-5.
// In particular `FieldElement` and `FieldCanvas` are defined.
// The `FieldCanvas` is an integer type with 131-bit (to hold 2*(2^130-5)).
// The `FieldElement` is a natural integer modulo 2^130-5.

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 131, // This amounts to 17 bytes
    modulo_value: "03fffffffffffffffffffffffffffffffb"
);

// Internal Poly1305 State
pub type PolyState = (FieldElement, FieldElement, PolyKey); //(accumulator,r,key)

pub fn poly1305_encode_r (b:&PolyBlock) -> FieldElement {
    let mut n = U128_from_le_bytes(U128Word::from_seq(b));
    n = n & U128(0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffffu128);
    FieldElement::from_secret_literal(n)
}

pub fn poly1305_encode_block (b:&PolyBlock) -> FieldElement {
    let n = U128_from_le_bytes(U128Word::from_seq(b));
    let f = FieldElement::from_secret_literal(n);
    f + FieldElement::pow2(128)
}

// In Poly1305 as used in this spec, pad_len is always the length of b, i.e. there is no padding
// In Chacha20Poly1305, pad_len is set to BLOCKSIZE
pub fn poly1305_encode_last (pad_len:BlockIndex,b:&SubBlock) -> FieldElement {
    let n = U128_from_le_bytes(U128Word::from_slice(b,0,b.len())); 
    let f = FieldElement::from_secret_literal(n);
    f + FieldElement::pow2(8 * pad_len)
}

pub fn poly1305_init (k:PolyKey) -> PolyState {
    let r = poly1305_encode_r(&PolyBlock::from_slice(&k,0,16));
    (FieldElement::ZERO(), r, k)
}

pub fn poly1305_update_block (b:&PolyBlock, st:PolyState) -> PolyState {
    let (acc,r,k) = st;
    ((poly1305_encode_block(b) + acc) * r,r,k)
}

pub fn get_full_chunk(m:&Seq<U8>,cs:usize,i:usize) -> Seq<U8> {
    let (_len,block) = m.get_chunk(cs, i);
    block
}

pub fn get_last_chunk(m:&Seq<U8>,cs:usize) -> Seq<U8> {
    let nblocks = m.len() / cs;
    let (_len,block) = m.get_chunk(cs, nblocks);
    block
}

pub fn poly1305_update_blocks (m:&ByteSeq, st:PolyState) -> PolyState {
    let mut st = st;
    let nblocks = m.len() / BLOCKSIZE;
    for i in 0..nblocks {
        let block = PolyBlock::from_seq(&get_full_chunk(m,BLOCKSIZE, i));
        st = poly1305_update_block(&block,st);
    }
    st
}

pub fn poly1305_update_last (pad_len:usize, b:&SubBlock, st:PolyState) -> PolyState {
    let mut st = st;
    if b.len() > 0 {
        let (acc,r,k) = st;
        st = ((poly1305_encode_last(pad_len,b) + acc) * r,r,k);
    }
    st
}

pub fn poly1305_update (m:&ByteSeq, st:PolyState) -> PolyState {
    let st = poly1305_update_blocks(m,st);
    let last = get_last_chunk(m,BLOCKSIZE);
    poly1305_update_last(last.len(),&last,st)
}

pub fn poly1305_finish (st:PolyState) -> Tag {
    let (acc,_,k) = st;
    let n = U128_from_le_bytes(U128Word::from_slice(&k,16,16));
// For some reason the little-endian version below does not work, but the big-endian version does.
//    let aby = acc.to_byte_seq_le();
//    let a = U128_from_le_bytes(U128Word::from_slice(&aby,0,16));
    let a = acc.to_byte_seq_be().slice(1, BLOCKSIZE);
    let a = U128_from_be_bytes(U128Word::from_seq(&a));
    Tag::from_seq(&U128_to_le_bytes(a+n))
}

pub fn poly1305(m: &ByteSeq, key: PolyKey) -> Tag {
    let mut st = poly1305_init(key);
    st = poly1305_update(m,st);
    poly1305_finish(st)
}

