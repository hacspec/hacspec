// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Type definitions for use in poly1305.
bytes!(KeyPoly, 32);

const BLOCKSIZE: usize = 16;

// These are type aliases for convenience
bytes!(Block, BLOCKSIZE);

// These are actual types; fixed-length arrays.
public_bytes!(Tag, BLOCKSIZE);

// This defines the field for modulo 2^130-5.
// In particular `FieldElement` and `FieldCanvas` are defined.
// The `FieldCanvas` is an integer type with 131-bit (to hold 2*(2^130-5)).
// The `FieldElement` is a natural integer modulo 2^130-5.
//
// XXX: The types are public here but should be secret. But secret BigNums are
// not implemented yet.
public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 131, // This amounts to 17 bytes
    modulo_value: "03fffffffffffffffffffffffffffffffb"
);

/// Take a variable length byte array and convert it into a U128 (secret u128).
pub fn le_bytes_to_num(b: &ByteSeq) -> U128 {
    let block_as_u128 = U128Word::from_slice(b, 0, min(BLOCKSIZE, b.len()));
    U128_from_le_bytes(block_as_u128)
}

/// Clamp a block `r` and return the resulting `FieldElement`.
pub fn clamp(r: U128) -> FieldElement {
    let r_uint = r & U128(0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffffu128);
    FieldElement::from_secret_literal(r_uint)
}

/// Convert a block (part of the byte sequence) to a `FieldElement`.
pub fn encode(block_uint: U128, len: usize) -> FieldElement {
    let w_elem = FieldElement::from_secret_literal(block_uint);
    let l_elem = FieldElement::pow2(8 * len);
    w_elem + l_elem
}

/// Convert the addition modulo 2^128 of two `FieldElement` to a `Tag` (16-byte array).
pub fn poly_finish(a: FieldElement, s: FieldElement) -> Tag {
    // The public slices representing a and s are 17 bytes
    // using big-endian representation; to get a modulo 2^128
    // we simply cut-off the left-most byte using slice.
    let a = a.to_public_byte_seq_be().slice(1, BLOCKSIZE);
    let a = u128_from_be_bytes(u128Word::from_seq(&a));
    let s = s.to_public_byte_seq_be().slice(1, BLOCKSIZE);
    let s = u128_from_be_bytes(u128Word::from_seq(&s));
    let a = a.wrapping_add(s);
    Tag::from_seq(&u128_to_le_bytes(a))
}

pub fn poly(m: &ByteSeq, key: KeyPoly) -> Tag {
    let r = le_bytes_to_num(&key.slice(0, BLOCKSIZE));
    let r = clamp(r);

    let s = le_bytes_to_num(&key.slice(BLOCKSIZE, BLOCKSIZE));
    let s = FieldElement::from_secret_literal(s);

    let mut a = FieldElement::from_literal(0u128);
    for i in 0..m.num_chunks(BLOCKSIZE) {
        let (len, block) = m.get_chunk(BLOCKSIZE, i);
        let block_uint = le_bytes_to_num(&block);
        let n = encode(block_uint, len);
        a = a + n;
        a = r * a;
    }
    poly_finish(a, s)
}
