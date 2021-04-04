// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(State, 16, U32, type_for_indexes: StateIdx);
bytes!(StateBytes, 64);
bytes!(IV, 12);
bytes!(Key, 32);

pub fn state_to_bytes(x: State) -> StateBytes {
    let mut r = StateBytes::new();
    for i in 0..x.len() {
        let bytes = U32_to_be_bytes(x[i]);
        r[i * 4] = bytes[3];
        r[i * 4 + 1] = bytes[2];
        r[i * 4 + 2] = bytes[1];
        r[i * 4 + 3] = bytes[0];
    }
    r
}

fn chacha_line(a: StateIdx, b: StateIdx, d: StateIdx, s: usize, m: State) -> State {
    let mut state = m;
    // TODO: we can't write += or ^= here right now :(
    state[a] = state[a] + state[b];
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

pub fn chacha_quarter_round(
    a: StateIdx,
    b: StateIdx,
    c: StateIdx,
    d: StateIdx,
    state: State,
) -> State {
    let state = chacha_line(a, b, d, 16, state);
    let state = chacha_line(c, d, b, 12, state);
    let state = chacha_line(a, b, d, 8, state);
    chacha_line(c, d, b, 7, state)
}

fn chacha_double_round(state: State) -> State {
    let state = chacha_quarter_round(0, 4, 8, 12, state);
    let state = chacha_quarter_round(1, 5, 9, 13, state);
    let state = chacha_quarter_round(2, 6, 10, 14, state);
    let state = chacha_quarter_round(3, 7, 11, 15, state);

    let state = chacha_quarter_round(0, 5, 10, 15, state);
    let state = chacha_quarter_round(1, 6, 11, 12, state);
    let state = chacha_quarter_round(2, 7, 8, 13, state);
    chacha_quarter_round(3, 4, 9, 14, state)
}

pub fn chacha20_constants_init() -> Seq<U32> {
    let mut constants = Seq::<U32>::new(4);
    constants[0] = U32(0x6170_7865u32);
    constants[1] = U32(0x3320_646eu32);
    constants[2] = U32(0x7962_2d32u32);
    constants[3] = U32(0x6b20_6574u32);
    constants
}

pub fn chacha20_key_to_u32s(key: Key) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(8);
    uints[0] = U32_from_le_bytes(U32Word::from_slice_range(&key, 0..4));
    uints[1] = U32_from_le_bytes(U32Word::from_slice_range(&key, 4..8));
    uints[2] = U32_from_le_bytes(U32Word::from_slice_range(&key, 8..12));
    uints[3] = U32_from_le_bytes(U32Word::from_slice_range(&key, 12..16));
    uints[4] = U32_from_le_bytes(U32Word::from_slice_range(&key, 16..20));
    uints[5] = U32_from_le_bytes(U32Word::from_slice_range(&key, 20..24));
    uints[6] = U32_from_le_bytes(U32Word::from_slice_range(&key, 24..28));
    uints[7] = U32_from_le_bytes(U32Word::from_slice_range(&key, 28..32));
    uints
}

pub fn chacha20_iv_to_u32s(iv: IV) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(3);
    uints[0] = U32_from_le_bytes(U32Word::from_slice_range(&iv, 0..4));
    uints[1] = U32_from_le_bytes(U32Word::from_slice_range(&iv, 4..8));
    uints[2] = U32_from_le_bytes(U32Word::from_slice_range(&iv, 8..12));
    uints
}

pub fn chacha20_ctr_to_seq(ctr: U32) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(1);
    uints[0] = ctr;
    uints
}

pub fn chacha_block_init(key: Key, ctr: U32, iv: IV) -> State {
    State::from_seq(
        &chacha20_constants_init()
            .concat(&chacha20_key_to_u32s(key))
            .concat(&chacha20_ctr_to_seq(ctr))
            .concat(&chacha20_iv_to_u32s(iv)),
    )
}

pub fn chacha_block_inner(key: Key, ctr: U32, iv: IV) -> State {
    let st = chacha_block_init(key, ctr, iv);
    let mut state = st;
    for _i in 0..10 {
        state = chacha_double_round(state);
    }
    for i in 0..16 {
        state[i] = state[i] + st[i];
    }
    state
}

pub fn chacha_block(key: Key, ctr: U32, iv: IV) -> StateBytes {
    let state = chacha_block_inner(key, ctr, iv);
    state_to_bytes(state)
}

pub fn chacha(key: Key, iv: IV, m: &ByteSeq) -> ByteSeq {
    let mut ctr = U32(1u32);
    let mut blocks_out = ByteSeq::new(m.len());
    for i in 0..m.num_exact_chunks(64) {
        let msg_block = m.get_exact_chunk(64, i);
        let msg_block = StateBytes::from_seq(&msg_block);
        let key_block = chacha_block(key, ctr, iv);
        blocks_out = blocks_out.set_chunk(64, i, &(msg_block ^ key_block));
        ctr = ctr + U32(1u32);
    }
    let last_block = m.get_remainder_chunk(64);
    if last_block.len() != 0 {
        let key_block = chacha_block(key, ctr, iv);
        let msg_block_padded = StateBytes::new();
        let msg_block_padded = msg_block_padded.update_start(&last_block);
        blocks_out = blocks_out.set_chunk(
            64,
            m.num_chunks(64) - 1,
            &(msg_block_padded ^ key_block).slice_range(0..last_block.len()),
        );
    }
    blocks_out
}
