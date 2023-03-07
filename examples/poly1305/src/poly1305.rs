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
bytes!(Poly1305Tag, 16);

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

// Internal Poly1305 State: (accumulator,r,s)
pub type PolyState = (FieldElement, FieldElement, U128);


// RFC 8439: 2.5.1.  The Poly1305 Algorithms in Pseudocode
///      clamp(r): r &= 0x0ffffffc0ffffffc0ffffffc0fffffff
///      poly1305_mac(msg, key):
///         r = le_bytes_to_num(key[0..15])
///         clamp(r)
///         s = le_bytes_to_num(key[16..31])
///         a = 0  /* a is the accumulator */
///         p = (1<<130)-5
///         for i=1 upto ceil(msg length in bytes / 16)
///            n = le_bytes_to_num(msg[((i-1)*16)..(i*16)] | [0x01])
///            a += n
///            a = (r * a) % p
///            end
///         a += s
///         return num_to_16_le_bytes(a)
///         end
	 
pub fn poly1305_encode_r(b: &PolyBlock) -> FieldElement {
    let mut n = U128_from_le_bytes(U128Word::from_seq(b));
    n = n & U128(0x0fff_fffc_0fff_fffc_0fff_fffc_0fff_ffffu128);
    FieldElement::from_secret_literal(n)
}

pub fn poly1305_init(k: PolyKey) -> PolyState {
    let r = poly1305_encode_r(&PolyBlock::from_slice(&k, 0, 16));
    let s = U128_from_le_bytes(U128Word::from_slice(&k, 16, 16));
    (FieldElement::ZERO(), r, s)
}

pub fn poly1305_encode_block(b: &PolyBlock) -> FieldElement {
    let n = U128_from_le_bytes(U128Word::from_seq(b));
    let f = FieldElement::from_secret_literal(n);
    f + FieldElement::pow2(128)
}

pub fn poly1305_update_block(b: &PolyBlock, (acc,r,s): PolyState) -> PolyState {
    ((poly1305_encode_block(b) + acc) * r, r, s)
}

pub fn poly1305_update_blocks(m: &ByteSeq, mut state: PolyState) -> PolyState {
    let n_blocks = m.num_exact_chunks(BLOCKSIZE);
    for i in 0..n_blocks {
        let block = PolyBlock::from_seq(&m.get_exact_chunk(BLOCKSIZE, i));
        state = poly1305_update_block(&block, state);
    }
    state
}

// In Poly1305 as used in this spec, pad_len is always the length of b, i.e. there is no padding
// In Chacha20Poly1305, pad_len is set to BLOCKSIZE
pub fn poly1305_encode_last(pad_len: BlockIndex, b: &SubBlock) -> FieldElement {
    let n = U128_from_le_bytes(U128Word::from_slice(b, 0, b.len()));
    let f = FieldElement::from_secret_literal(n);
    f + FieldElement::pow2(8 * pad_len)
}
pub fn poly1305_update_last(pad_len: usize, b: &SubBlock, mut state: PolyState) -> PolyState {
    if b.len() != 0 {
        let (acc,r,s) = state;
        state = ((poly1305_encode_last(pad_len, b) + acc) * r, r, s);
    }
    state
}

pub fn poly1305_update(m: &ByteSeq, mut state: PolyState) -> PolyState {
    state = poly1305_update_blocks(m, state);
    let last = m.get_remainder_chunk(BLOCKSIZE);
    poly1305_update_last(last.len(), &last, state)
}

pub fn poly1305_finish((acc,_,s): PolyState) -> Poly1305Tag {
    let aby = acc.to_byte_seq_le();
    // We can't use from_seq here because the accumulator is larger than 16 bytes.
    let a = U128_from_le_bytes(U128Word::from_slice(&aby, 0, 16));
    Poly1305Tag::from_seq(&U128_to_le_bytes(a + s))
}

pub fn poly1305(m: &ByteSeq, key: PolyKey) -> Poly1305Tag {
    let mut state = poly1305_init(key);
    state = poly1305_update(m, state);
    poly1305_finish(state)
}
