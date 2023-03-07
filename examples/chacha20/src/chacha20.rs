// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(State, 16, U32, type_for_indexes: StateIdx);
array!(Constants, 4, U32, type_for_indexes: ConstantsIdx);
bytes!(Block, 64);
bytes!(ChaChaNonce, 12);
bytes!(ChaChaKey, 32);

// === RFC 8439: ChaCha20 and Poly1305 for IETF Protocols
// === 2.1.  The ChaCha Quarter Round

///  a += b; d ^= a; d <<<= 16;
///  c += d; b ^= c; b <<<= 12;
///  a += b; d ^= a; d <<<= 8;
///  c += d; b ^= c; b <<<= 7;

fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: usize, mut state: State) -> State {
    state[a] = state[a] + state[b];
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

pub fn chacha20_quarter_round(
    a: StateIdx,
    b: StateIdx,
    c: StateIdx,
    d: StateIdx,
    mut state: State,
) -> State {
    state = chacha20_line(a, b, d, 16, state);
    state = chacha20_line(c, d, b, 12, state);
    state = chacha20_line(a, b, d, 8, state);
    chacha20_line(c, d, b, 7, state)
}

// === 2.3.1.  The ChaCha20 Block Function in Pseudocode
/// inner_block (state):
///         Qround(state, 0, 4, 8,12)
///         Qround(state, 1, 5, 9,13)
///         Qround(state, 2, 6,10,14)
///         Qround(state, 3, 7,11,15)
///         Qround(state, 0, 5,10,15)
///         Qround(state, 1, 6,11,12)
///         Qround(state, 2, 7, 8,13)
///         Qround(state, 3, 4, 9,14)
///         end

fn inner_block(mut state: State) -> State {
    state = chacha20_quarter_round(0, 4, 8, 12, state);
    state = chacha20_quarter_round(1, 5, 9, 13, state);
    state = chacha20_quarter_round(2, 6, 10, 14, state);
    state = chacha20_quarter_round(3, 7, 11, 15, state);
    state = chacha20_quarter_round(0, 5, 10, 15, state);
    state = chacha20_quarter_round(1, 6, 11, 12, state);
    state = chacha20_quarter_round(2, 7, 8, 13, state);
    chacha20_quarter_round(3, 4, 9, 14, state)
}

/// chacha20_block(key, counter, nonce):
///         state = constants | key | counter | nonce
///         working_state = state
///         for i=1 upto 10
///            inner_block(working_state)
///            end
///         state += working_state
///         return serialize(state)
///         end

const CHACHA20_CONSTANTS: Constants = Constants(secret_array!(
    U32,
    [0x6170_7865u32, 0x3320_646eu32, 0x7962_2d32u32, 0x6b20_6574u32]));

pub fn chacha20_init(key: ChaChaKey, counter: U32, nonce: ChaChaNonce) -> State {
    let mut state = State::new();
    state = state.update(0, &CHACHA20_CONSTANTS);
    state = state.update(4, &key.to_le_U32s());
    state[12] = counter;
    state = state.update(13, &nonce.to_le_U32s());
    state
}

pub fn chacha20_rounds(mut working_state: State) -> State {
    for _i in 0..10 {
        working_state = inner_block(working_state);
    }
    working_state
}

pub fn chacha20_core(ctr: U32, mut state: State) -> State {
    state[12] = state[12] + ctr;
    let working_state = chacha20_rounds(state);
    working_state + state
}

pub fn chacha20_key_block(state: State) -> Block {
    let state = chacha20_core(U32(0u32), state);
    Block::from_seq(&state.to_le_bytes())
}

pub fn chacha20_key_block0(key: ChaChaKey, nonce: ChaChaNonce) -> Block {
    let state = chacha20_init(key, U32(0u32), nonce);
    chacha20_key_block(state)
}

pub fn chacha20_encrypt_block(st0: State, counter: U32, plain: &Block) -> Block {
    let mut state = chacha20_core(counter, st0);
    let pl = State::from_seq(&plain.to_le_U32s());
    state = pl ^ state;
    Block::from_seq(&state.to_le_bytes())
}

pub fn chacha20_encrypt_last(st0: State, ctr: U32, plain: &ByteSeq) -> ByteSeq {
    let mut b = Block::new();
    b = b.update(0, plain);
    b = chacha20_encrypt_block(st0, ctr, &b);
    b.slice(0, plain.len())
}

pub fn chacha20_update(st0: State, m: &ByteSeq) -> ByteSeq {
    let mut blocks_out = ByteSeq::new(m.len());
    let n_blocks = m.num_exact_chunks(64);
    for i in 0..n_blocks {
        let msg_block = m.get_exact_chunk(64, i);
        let b = chacha20_encrypt_block(st0, U32(i as u32), &Block::from_seq(&msg_block));
        blocks_out = blocks_out.set_exact_chunk(64, i, &b);
    }
    let last_block = m.get_remainder_chunk(64);
    if last_block.len() != 0 {
        let b = chacha20_encrypt_last(st0, U32(n_blocks as u32), &last_block);
        blocks_out = blocks_out.set_chunk(64, n_blocks, &b);
    }
    blocks_out
}

pub fn chacha20(key: ChaChaKey, nonce: ChaChaNonce, ctr: u32, m: &ByteSeq) -> ByteSeq {
    let state = chacha20_init(key, U32(ctr), nonce);
    chacha20_update(state, m)
}
