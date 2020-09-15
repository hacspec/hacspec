use secret_integers::*;

const BLOCK_SIZE: usize = 64;
type State = [U32; 16];
type Key = Vec<U8>;
type Nonce = Vec<U8>;
type Block = [U8; 64];
type Constants = [u32; 4];
type Index = usize;
type RotVal = usize;

pub fn classify_u32s(v: &[u32]) -> Vec<U32> {
    v.iter().map(|x| U32::classify(*x)).collect()
}

fn line(a: Index, b: Index, d: Index, s: RotVal, m: &mut State) {
    m[a] = m[a] + m[b];
    m[d] = m[d] ^ m[a];
    m[d] = m[d].rotate_left(s);
}

fn quarter_round(a: Index, b: Index, c: Index, d: Index, m: &mut State) {
    line(a, b, d, 16, m);
    line(c, d, b, 12, m);
    line(a, b, d, 8, m);
    line(c, d, b, 7, m);
}

fn double_round(m: &mut State) {
    quarter_round(0, 4, 8, 12, m);
    quarter_round(1, 5, 9, 13, m);
    quarter_round(2, 6, 10, 14, m);
    quarter_round(3, 7, 11, 15, m);

    quarter_round(0, 5, 10, 15, m);
    quarter_round(1, 6, 11, 12, m);
    quarter_round(2, 7, 8, 13, m);
    quarter_round(3, 4, 9, 14, m);
}

const CONSTANTS: Constants = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

fn chacha20_init(k: &Key, counter: U32, nonce: &Nonce) -> State {
    let mut st = [U32::classify(0u32); 16];
    st[0..4].copy_from_slice(&classify_u32s(&CONSTANTS));
    st[4..12].copy_from_slice(U32::from_le_bytes(k).as_slice());
    st[12] = counter;
    st[13..16].copy_from_slice(U32::from_le_bytes(nonce).as_slice());
    st
}

fn chacha20_core(st: &mut State) {
    let mut working_state = st.clone();
    for _ in 0..10 {
        double_round(&mut working_state);
    }
    for i in 0..16 {
        st[i] += working_state[i];
    }
}

fn chacha20(k: &Key, counter: U32, nonce: &Nonce) -> State {
    let mut st = chacha20_init(k, counter, nonce);
    chacha20_core(&mut st);
    st
}

fn chacha20_block(k: &Key, counter: U32, nonce: &Nonce) -> Block {
    let st = chacha20(k, counter, nonce);
    let mut block = [U8::classify(0u8); BLOCK_SIZE];
    block.copy_from_slice(U32::to_le_bytes(&st).as_slice());
    block
}

fn xor_block(block: &Block, key_block: &Block) -> Block {
    let mut v_out = [Default::default(); BLOCK_SIZE];
    for i in 0..BLOCK_SIZE {
        v_out[i] = block[i] ^ key_block[i];
    }
    let mut out = [Default::default(); BLOCK_SIZE];
    out.copy_from_slice(&v_out);
    out
}

fn chacha20_counter_mode(key: &Key, counter: U32, nonce: &Nonce, msg: &Vec<U8>) -> Vec<U8> {
    let mut blocks: Vec<[U8; BLOCK_SIZE]> = msg
        .chunks(BLOCK_SIZE)
        .map(|block| {
            let mut new_block = [U8::zero(); BLOCK_SIZE];
            new_block[0..block.len()].copy_from_slice(block);
            new_block
        })
        .collect();
    let nb_blocks = blocks.len();
    let mut key_block: [U8; BLOCK_SIZE];
    let mut ctr = counter;
    for i in 0..blocks.len() - 1 {
        key_block = chacha20_block(key, ctr, nonce);
        blocks[i] = xor_block(&blocks[i], &key_block);
        ctr += U32::one();
    }
    let last = &mut blocks[nb_blocks - 1];
    key_block = chacha20_block(key, ctr, nonce);
    *last = xor_block(last, &key_block);
    blocks
        .iter()
        .map(|block| block.to_vec())
        .flatten()
        .take(msg.len())
        .collect()
}

pub fn chacha20_encrypt(key: &Key, counter: U32, nonce: &Nonce, msg: &Vec<U8>) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}

pub fn chacha20_decrypt(key: &Key, counter: U32, nonce: &Nonce, msg: &Vec<U8>) -> Vec<U8> {
    chacha20_counter_mode(key, counter, nonce, msg)
}
