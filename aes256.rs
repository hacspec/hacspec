// Import hacspec and all needed definitions.
use hacspec::prelude::*;
// TODO: move to hacspec_imports if we want to use it!
use contracts::*;
// I need 32 bytes for a AES256 key CHANGED FROM 16 to 32
const BLOCKSIZE: usize = 32;
// CHANGED from 12 to 28, not sure if it is right
const IVSIZE: usize = 12;

bytes!(Block, BLOCKSIZE);
bytes!(Word, 4);
bytes!(Key, BLOCKSIZE);
// TODO is it random,secure if we leave 4 bytes undefined?
bytes!(Nonce, IVSIZE);
bytes!(SBox, 256);
// CHANGE FROM 11 to 15
bytes!(RCon, 15);
bytes!(Bytes208, 208);
bytes!(Bytes240, 240);


const SBOX: SBox = SBox(secret_bytes!([
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16
]));

const RCON: RCon = RCon(secret_bytes!([
    0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d
]));

fn sub_bytes(state: Block) -> Block {
    let mut st = state;
    for i in 0..BLOCKSIZE {
        st[i] = SBOX[U8::declassify(state[i])];
    }
    st
}


#[pre(i < 4)]
#[pre(shift < 8)]
fn shift_row(i: usize, shift: usize, state: Block) -> Block {
    let mut out = state;
    out[i] = state[i + (4 * (shift % 8))];
    out[i + 4] = state[i + (4 * ((shift + 1) % 8))];
    out[i + 8] = state[i + (4 * ((shift + 2) % 8))];
    out[i + 12] = state[i + (4 * ((shift + 3) % 8))];
    out[i + 16] = state[i + (4 * ((shift + 4) % 8))];
    out[i + 16] = state[i + (4 * ((shift + 4) % 8))];
    out[i + 20] = state[i + (4 * ((shift + 5) % 8))];
    out[i + 24] = state[i + (4 * ((shift + 6) % 8))];
    out[i + 28] = state[i + (4 * ((shift + 7) % 8))];
    out
}

fn shift_rows(state: Block) -> Block {
    let state = shift_row(1, 1, state);
    let state = shift_row(2, 2, state);
    shift_row(3, 3, state)
}

fn xtime(x: U8) -> U8 {
    let x1 = x << 1;
    let x7 = x >> 7;
    let x71 = x7 & U8(0x01);
    let x711b = x71 * U8(0x1b);
    x1 ^ x711b
}

#[pre(c < 8)]
fn mix_column(c: usize, state: Block) -> Block {
    let i0 = 4 * c;
    let s0 = state[i0];
    let s1 = state[i0 + 1];
    let s2 = state[i0 + 2];
    let s3 = state[i0 + 3];
    let mut st = state;
    let tmp = s0 ^ s1 ^ s2 ^ s3;
    st[i0] = s0 ^ tmp ^ (xtime(s0 ^ s1));
    st[i0 + 1] = s1 ^ tmp ^ (xtime(s1 ^ s2));
    st[i0 + 2] = s2 ^ tmp ^ (xtime(s2 ^ s3));
    st[i0 + 3] = s3 ^ tmp ^ (xtime(s3 ^ s0));
    st
}
// CHANGE FROM 4 to 8 ROWS
fn mix_columns(state: Block) -> Block {
    let state = mix_column(0, state);
    let state = mix_column(1, state);
    let state = mix_column(2, state);
    let state = mix_column(3, state);
    let state = mix_column(4, state);
    let state = mix_column(5, state);
    let state = mix_column(6, state);
    mix_column(7, state)

}

fn add_round_key(state: Block, key: Key) -> Block {
    let mut out = state;
    for i in 0..BLOCKSIZE {
        out[i] ^= key[i];
    }
    out
}

fn aes_enc(state: Block, round_key: Key) -> Block {
    let state = sub_bytes(state);
    let state = shift_rows(state);
    let state = mix_columns(state);
    add_round_key(state, round_key)
}

fn aes_enc_last(state: Block, round_key: Key) -> Block {
    let state = sub_bytes(state);
    let state = shift_rows(state);
    add_round_key(state, round_key)
}

fn rounds(state: Block, key: Bytes208) -> Block {
    let mut out = state;
    for (_, key_block) in key.chunks(BLOCKSIZE) {
        out = aes_enc(out, Key::from(key_block));
    }
    out
}

fn block_cipher(input: Block, key: Bytes240) -> Block {
    let k0 = Key::from_sub(key, 0..32);
    let k = Bytes208::from_sub(key, 32..15 * 16);
    let kn = Key::from_sub(key, 15 * 16..16 * 17);
    let state = add_round_key(input, k0);
    let state = rounds(state, k);
    aes_enc_last(state, kn)
}

fn rotate_word(w: Word) -> Word {
    Word([w[1], w[2], w[3], w[0]])
}

fn sub_word(w: Word) -> Word {
    Word([
        SBOX[usize::from(w[0])],
        SBOX[usize::from(w[1])],
        SBOX[usize::from(w[2])],
        SBOX[usize::from(w[3])],
    ])
}

fn aes_keygen_assist(w: Word, rcon: U8) -> Word {
    let mut k = rotate_word(w);
    k = sub_word(k);
    k[0] ^= rcon;
    k
}
// CHANGE 44 to 60 and the if clause 
/*fn key_expansion_word(w0: Word, w1: Word, i: usize) -> Word {
    assert!(i < 60);
    let mut k = w1;
    if i % 8 == 0 {
        k = aes_keygen_assist(k, RCON[i / 8]);
    } else if i % 8 == 4 {
        k = sub_word(k);
    }
    for i in 0..4 {
        k[i] ^= w0[i];
    }
    k
}*/
//  
fn key_expansion_new(w0: Word, w1: Word, i: usize) -> Word {
    assert!(i < 60);
    let mut k = w1;
    if i % 8 == 0 {
        k = aes_keygen_assist(k, RCON[i / 8]);
    } else if i % 8 == 4 {
        k = sub_word(k);
    }
    for i in 0..4 {
        k[i] ^= w0[i];
    }
    k
}

// CHANGED 0..40 TO 0..52
//( https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf) 
fn key_expansion(key: Key) -> Bytes240 {
    let mut key_ex = Bytes240::from(key.raw());
    let mut i: usize;
    for j in 0..52 {
        // CHANGED FROM +4 TO +8
        i = j + 8;
        let word = key_expansion_new(
            Word::from_sub(key_ex, 4 * i - 32..4 * i - 28),
            Word::from_sub(key_ex, 4 * i - 4..4 * i),
            i,
        );
        key_ex = key_ex.update(4 * i, word);
    }
    key_ex
}

fn aes256_encrypt_block(k: Key, input: Block) -> Block {
    let key_ex = key_expansion(k);
    block_cipher(input, key_ex)
}

pub(crate) fn aes256_ctr_keyblock(k: Key, n: Nonce, c: U32) -> Block {
    let mut input = Block::new();
    input = input.update(0, n);
    input = input.update(12, u32_to_be_bytes(c));
    aes256_encrypt_block(k, input)
}

pub(crate) fn xor_block(block: Block, keyblock: Block) -> Block {
    let mut out = block;
    for i in 0..BLOCKSIZE {
        out[i] ^= keyblock[i];
    }
    out
}

fn aes256_counter_mode(key: Key, nonce: Nonce, counter: U32, msg: ByteSeq) -> ByteSeq {
    let mut ctr = counter;
    let mut blocks_out = ByteSeq::new(msg.len());
    for (block_len, msg_block) in msg.chunks(BLOCKSIZE) {
        if msg_block.len() == BLOCKSIZE {
            let key_block = aes256_ctr_keyblock(key, nonce, ctr);
            blocks_out = blocks_out.push(
                xor_block(Block::from(msg_block), key_block),
            );
            ctr += U32(1);
        } else {
            // Last block that needs padding
            let keyblock = aes256_ctr_keyblock(key, nonce, ctr);
            let last_block = Block::from(msg_block);
            blocks_out = blocks_out.push_sub(xor_block(last_block, keyblock), 0, block_len);
        }
    }
    blocks_out
}

pub fn aes256_encrypt(key: Key, nonce: Nonce, counter: U32, msg: ByteSeq) -> ByteSeq {
    aes256_counter_mode(key, nonce, counter, msg)
}

pub fn aes256_decrypt(key: Key, nonce: Nonce, counter: U32, ctxt: ByteSeq) -> ByteSeq {
    aes256_counter_mode(key, nonce, counter, ctxt)
}

// Testing some internal functions.

#[test]
#[should_panic]
fn test_contract1() {
    shift_row(4, 3, Block::new());
}

#[test]
#[should_panic]
fn test_contract2() {
    shift_row(2, 4, Block::new());
}

#[test]
fn test_ty_block(){
    let msg = ByteSeq::from_array(&secret_bytes!([
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9,0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17,
        0x2a, 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9,0x3d, 0x7e, 0x11, 0x73, 0x93,
         0x17,0x2a
         ]));
    let key = Key(secret_bytes!([
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
        ]));
    let nonce = Nonce(secret_bytes!([
            0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb
        ]));
    let ctr = U32(0xfcfdfeff);

    let ctxt = ByteSeq::from_array(&secret_bytes!([
        0x18, 0xe6, 0xf1, 0xbc, 0x27, 0x8f, 0xe6, 0x69, 0x65, 0xa8, 0xef, 0xd4, 0x73, 0xc6, 0x3f, 0x3c, 0x31,
        0x6f, 0xd9, 0x86, 0xe9, 0xc3, 0x0a, 0xa4, 0xfc, 0xab, 0x04, 0x68, 0x91, 0xcf, 0x13, 0xfd
        ]));
    let c = aes256_encrypt(key,nonce,ctr ,msg);
    assert_bytes_eq!(ctxt, c);
}
/*#[test]
fn test_kat_block1() {
    let msg = Block(secret_bytes!([
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17,
        0x2a
    ]));
    let key = Key(secret_bytes!([
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f,
        0x3c, 0x8f, 0x12, 0xe2, 0x00, 0xed, 0x12, 0x3c, 0x8f, 0x12, 0xe2, 0x00 , 0xed, 0x12, 0x73,
        0xae, 0xff
    ]));
    let ctxt = secret_bytes!([
        0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef,
        0x97
    ]);

    let c = aes256_encrypt_block(key, msg);
    assert_bytes_eq!(ctxt, c);
}*/
/*
#[test]
fn test_kat_block2() {
    let msg = Block(secret_bytes!([
        0x53, 0x69, 0x6e, 0x67, 0x6c, 0x65, 0x20, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x20, 0x6d, 0x73,
        0x67
    ]));
    let key = Key(secret_bytes!([
        0xae, 0x68, 0x52, 0xf8, 0x12, 0x10, 0x67, 0xcc, 0x4b, 0xf7, 0xa5, 0x76, 0x55, 0x77, 0xf3,
        0x9e
    ]));
    let ctxt = ByteSeq::from_array(&secret_bytes!([
        0x61, 0x5f, 0x09, 0xfb, 0x35, 0x3f, 0x61, 0x3b, 0xa2, 0x8f, 0xf3, 0xa3, 0x0c, 0x64, 0x75,
        0x2d
    ]));
    let c = aes256_encrypt_block(key, msg);
    assert_bytes_eq!(ctxt, c);
}
*/
