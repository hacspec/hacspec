use hacspec_lib::*;

array!(State, 12, U32, type_for_indexes: StateIdx);

fn swap(mut s: State, i: StateIdx, j: StateIdx) -> State {
    let tmp = s[i];
    s[i] = s[j];
    s[j] = tmp;
    s
}

fn gimli_round(mut s: State, r: u32) -> State {
    for col in 0usize..4 {
        let x = s[col].rotate_left(24);
        let y = s[col + 4].rotate_left(9);
        let z = s[col + 8];

        s[col + 8] = x ^ (z << 1) ^ ((y & z) << 2);
        s[col + 4] = y ^ x ^ ((x | z) << 1);
        s[col] = z ^ y ^ ((x & y) << 3);
    }

    if (r & 3u32) == 0u32 {
        s = swap(s, 0, 1);
        s = swap(s, 2, 3);
    }

    if (r & 3u32) == 2u32 {
        s = swap(s, 0, 2);
        s = swap(s, 1, 3);
    }

    if (r & 3u32) == 0u32 {
        s[0] = s[0] ^ (U32(0x9e377900u32) | U32(r))
    }

    s
}

pub fn gimli(mut s: State) -> State {
    for rnd in 0..24 { // XXX: Why do we only allow usize loops?
        s = gimli_round(s, (24 - rnd) as u32)
    }

    s
}

// === Hash ===

bytes!(Block, 16);
bytes!(Digest, 32);

fn absorb_block(input_block: Block, mut s: State) -> State {
    let input_bytes = input_block.to_le_U32s();
    s[0] = s[0] ^ input_bytes[0];
    s[1] = s[1] ^ input_bytes[1];
    s[2] = s[2] ^ input_bytes[2];
    s[3] = s[3] ^ input_bytes[3];
    gimli(s)
}

fn squeeze_block(s: State) -> Block {
    let mut block = Block::new();
    for i in 0..4 {
        let s_i: U32 = s[i]; // XXX: Rust can't figure out the type here for some reason.
        let s_i_bytes = s_i.to_le_bytes();
        block[4 * i] = s_i_bytes[0];
        block[4 * i + 1] = s_i_bytes[1];
        block[4 * i + 2] = s_i_bytes[2];
        block[4 * i + 3] = s_i_bytes[3];
    }
    block
}

pub fn gimli_hash(input_bytes: &ByteSeq) -> Digest {
    let mut s = State::new();

    let rate = Block::length();
    for i in 0..input_bytes.num_chunks(rate) {
        let (block_len, input_block) = input_bytes.get_chunk(rate, i);
        if block_len == rate {
            // Absorb full blocks
            let full_block = Block::from_seq(&input_block);
            s = absorb_block(full_block, s);
        } else {
            // Absorb last incomplete block
            // Note that this would work in all other cases as well, but the above is safer.
            let input_block_padded = Block::new();
            let mut input_block_padded = input_block_padded.update_start(&input_block);
            input_block_padded[block_len] = U8(1u8);

            // XOR in capacity part
            s[11] = s[11] ^ U32(0x01000000u32);
            s = absorb_block(input_block_padded, s);
        }
    }

    let output = Digest::new();
    let output = output.update_start(&squeeze_block(s));
    s = gimli(s);
    output.update(rate, &squeeze_block(s))
}
