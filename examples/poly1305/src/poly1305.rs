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

pub fn poly1305_encode_block (len:usize, b:&SubBlock) -> FieldElement {
    let n = U128_from_le_bytes(U128Word::from_slice(b,0,b.len())); // Silliness, from_seq should work but it panics
    let f = FieldElement::from_secret_literal(n);
    f + FieldElement::pow2(8 * len)
}

pub fn poly1305_init (k:PolyKey) -> PolyState {
    let r = poly1305_encode_r(&PolyBlock::from_slice(&k,0,16));
    (FieldElement::ZERO(), r, k)
}

pub fn poly1305_update1 (len:usize, b:&SubBlock, st:PolyState) -> PolyState {
    let (acc,r,k) = st;
    ((poly1305_encode_block(len,b) + acc) * r,r,k)
}

pub fn poly1305_finish (st:PolyState) -> Tag {
    let (acc,_,k) = st;
    let n = U128_from_le_bytes(U128Word::from_slice(&k,16,16));
    let aby = acc.to_byte_seq_le();
    let a = U128_from_le_bytes(U128Word::from_slice(&aby,0,16)); // Silliness, from_seq should work but it panics
    Tag::from_seq(&U128_to_le_bytes(a+n))
}

pub fn poly1305_update (m:&ByteSeq, st:PolyState) -> PolyState {
    let mut st = st;
    for i in 0..m.num_chunks(BLOCKSIZE) {
        let (len, block) = m.get_chunk(BLOCKSIZE, i);
        st = poly1305_update1(len,&block,st);
    }
    st
}

pub fn poly1305(m: &ByteSeq, key: PolyKey) -> Tag {
    let mut st = poly1305_init(key);
    st = poly1305_update(m,st);
    poly1305_finish(st)
}
