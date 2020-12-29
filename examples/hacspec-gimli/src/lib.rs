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
    for rnd in 0..24 {
        let rnd = (24 - rnd) as u32;
        s = gimli_round(s, rnd);
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

fn gimli_hash_state(input: &ByteSeq, mut s: State) -> State {
    let rate = Block::length();
    for i in 0..input.num_chunks(rate) {
        let (block_len, input_block) = input.get_chunk(rate, i);
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

    s
}

pub fn gimli_hash(input_bytes: &ByteSeq) -> Digest {
    let s = State::new();
    let s = gimli_hash_state(input_bytes, s);
    let output = Digest::new();
    let output = output.update_start(&squeeze_block(s));
    let s = gimli(s);
    output.update(Block::length(), &squeeze_block(s))
}

// === Cipher ===

bytes!(Nonce, 16);
bytes!(Key, 32);
bytes!(Tag, 16);

fn process_ad(ad: &ByteSeq, s: State) -> State {
    gimli_hash_state(ad, s)
}

fn process_msg(message: &ByteSeq, mut s: State) -> (State, ByteSeq) {
    let mut ciphertext = ByteSeq::new(message.len());

    let rate = Block::length();
    let num_chunks = message.num_chunks(rate);
    for i in 0..num_chunks {
        let key_block = squeeze_block(s);
        let (block_len, msg_block) = message.get_chunk(rate, i);

        // This pads the msg_block if necessary.
        let msg_block_padded = Block::new();
        let mut msg_block_padded = msg_block_padded.update_start(&msg_block);

        ciphertext = ciphertext.set_chunk(
            rate,
            i,
            // the slice_range cuts off the last block if it is padded
            &(msg_block_padded ^ key_block).slice_range(0..block_len),
        );
        if i == num_chunks - 1 {
            // XXX: this is in the code but I don't see it in the spec.
            msg_block_padded[block_len] = msg_block_padded[block_len] ^ U8(1u8);
            s[11] = s[11] ^ U32(0x01000000u32); // s_2,3
        }
        s = absorb_block(msg_block_padded, s);
    }

    (s, ciphertext)
}

fn process_ct(ciphertext: &ByteSeq, mut s: State) -> (State, ByteSeq) {
    let mut message = ByteSeq::new(ciphertext.len());

    let rate = Block::length();
    let num_chunks = ciphertext.num_chunks(rate);
    for i in 0..num_chunks {
        let key_block = squeeze_block(s);
        let (block_len, ct_block) = ciphertext.get_chunk(rate, i);

        // This pads the ct_block if necessary.
        let ct_block_padded = Block::new();
        let ct_block_padded = ct_block_padded.update_start(&ct_block);
        let mut msg_block = ct_block_padded ^ key_block;

        // Slice_range cuts off the msg_block to the actual length.
        message = message.set_chunk(rate, i, &msg_block.slice_range(0..block_len));
        if i == num_chunks - 1 {
            // XXX: this is in the code but I don't see it in the spec.
            msg_block[block_len] = msg_block[block_len] ^ U8(1u8);
            s[11] = s[11] ^ U32(0x01000000u32); // s_2,3
        }
        s = absorb_block(msg_block, s);
    }

    (s, message)
}

// XXX: These two functions should maybe get a helper in the library.
pub fn nonce_to_u32s(nonce: Nonce) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(4);
    uints[0] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 0..4));
    uints[1] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 4..8));
    uints[2] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 8..12));
    uints[3] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 12..16));
    uints
}

pub fn key_to_u32s(key: Key) -> Seq<U32> {
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

pub fn gimli_aead_encrypt(
    message: &ByteSeq,
    ad: &ByteSeq,
    nonce: Nonce,
    key: Key,
) -> (ByteSeq, Tag) {
    // Add nonce and key to state
    let s = State::from_seq(&nonce_to_u32s(nonce).concat(&key_to_u32s(key)));
    let s = gimli(s);

    let s = process_ad(ad, s);
    let (s, ciphertext) = process_msg(message, s);

    let tag = squeeze_block(s);
    let tag = Tag::from_seq(&tag);

    (ciphertext, tag)
}

pub fn gimli_aead_decrypt(
    ciphertext: &ByteSeq,
    ad: &ByteSeq,
    tag: Tag,
    nonce: Nonce,
    key: Key,
) -> ByteSeq {
    // Add nonce and key to state
    let s = State::from_seq(&nonce_to_u32s(nonce).concat(&key_to_u32s(key)));
    let s = gimli(s);

    let s = process_ad(ad, s);
    let (s, message) = process_ct(ciphertext, s);

    let my_tag = squeeze_block(s);
    let my_tag = Tag::from_seq(&my_tag);

    let mut out = ByteSeq::new(0);
    if my_tag.equal(tag) {
        out = message;
    };

    out
}
