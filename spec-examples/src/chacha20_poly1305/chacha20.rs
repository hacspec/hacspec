// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(State, 16, U32);
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

fn line(a: u32, b: u32, d: u32, s: u32, m: State) -> State {
    let mut state = m;
    // TODO: we can't write += or ^= here right now :(
    state[a] = state[a] + state[b];
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

pub fn quarter_round(a: u32, b: u32, c: u32, d: u32, state: State) -> State {
    let state = line(a, b, d, 16, state);
    let state = line(c, d, b, 12, state);
    let state = line(a, b, d, 8, state);
    line(c, d, b, 7, state)
}

fn double_round(state: State) -> State {
    let state = quarter_round(0, 4, 8, 12, state);
    let state = quarter_round(1, 5, 9, 13, state);
    let state = quarter_round(2, 6, 10, 14, state);
    let state = quarter_round(3, 7, 11, 15, state);

    let state = quarter_round(0, 5, 10, 15, state);
    let state = quarter_round(1, 6, 11, 12, state);
    let state = quarter_round(2, 7, 8, 13, state);
    quarter_round(3, 4, 9, 14, state)
}

pub fn block_init(key: Key, ctr: U32, iv: IV) -> State {
    State([
        U32(0x6170_7865),
        U32(0x3320_646e),
        U32(0x7962_2d32),
        U32(0x6b20_6574),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 0..4)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 4..8)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 8..12)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 12..16)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 16..20)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 20..24)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 24..28)),
        U32_from_le_bytes(U32Word::from_slice_range(&key, 28..32)),
        ctr,
        U32_from_le_bytes(U32Word::from_slice_range(&iv, 0..4)),
        U32_from_le_bytes(U32Word::from_slice_range(&iv, 4..8)),
        U32_from_le_bytes(U32Word::from_slice_range(&iv, 8..12)),
    ])
}

pub fn block_inner(key: Key, ctr: U32, iv: IV) -> State {
    let st = block_init(key, ctr, iv);
    let mut state = st;
    for _ in 0..10 {
        state = double_round(state);
    }
    for i in 0..16 {
        state[i] = state[i] + st[i];
    }
    state
}

pub fn block(key: Key, ctr: U32, iv: IV) -> StateBytes {
    let state = block_inner(key, ctr, iv);
    state_to_bytes(state)
}

pub fn chacha(key: Key, iv: IV, m: &ByteSeq) -> Result<ByteSeq, String> {
    let mut ctr = U32(1);
    let mut blocks_out = ByteSeq::new(m.len());
    for i in 0..m.num_chunks(64) {
        let (block_len, msg_block) = m.get_chunk(64, i);
        let key_block = block(key, ctr, iv);
        let msg_block_padded = StateBytes::new();
        let msg_block_padded = msg_block_padded.update_start(&msg_block);
        blocks_out = blocks_out.set_chunk(64, i, &(msg_block_padded ^ key_block).slice_range(0..block_len));
        ctr += U32(1);
    }
    Ok(blocks_out)
}
