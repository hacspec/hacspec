// Import hacspec and all needed definitions.
use hacspec_lib::*;

const BLOCK_SIZE: usize = 64;
const LEN_SIZE: usize = 8;
pub const K_SIZE: usize = 64;
pub const HASH_SIZE: usize = 256 / 8;

bytes!(Block, BLOCK_SIZE);
array!(OpTableType, 12, usize);
bytes!(Sha256Digest, HASH_SIZE);
array!(RoundConstantsTable, K_SIZE, U32);
array!(Hash, 8, U32);

pub fn ch(x: U32, y: U32, z: U32) -> U32 {
    (x & y) ^ ((!x) & z)
}

pub fn maj(x: U32, y: U32, z: U32) -> U32 {
    (x & y) ^ ((x & z) ^ (y & z))
}

// const BLOCK_SIZE: usize = 64;
// const LEN_SIZE: usize = 8;
// pub const K_SIZE: usize = 64;
// pub const HASH_SIZE: usize = 256 / 8;

// bytes!(Block, BLOCK_SIZE);
// array!(OpTableType, 12, usize);
// bytes!(Sha256Digest, HASH_SIZE);
// array!(RoundConstantsTable, K_SIZE, U32);
// array!(Hash, 8, U32);

// fn ch(x: U32, y: U32, z: U32) -> U32 {
//     (x & y) ^ ((!x) & z)
// }

pub fn sigma(x: U32, i: usize, op: usize) -> U32 {
    let mut tmp: U32 = x.rotate_right(OP_TABLE[3 * i + 2]);
    if op == 0 {
        tmp = x >> OP_TABLE[3 * i + 2]
    }
    x.rotate_right(OP_TABLE[3 * i]) ^ x.rotate_right(OP_TABLE[3 * i + 1]) ^ tmp
}

pub fn schedule(block: Block) -> RoundConstantsTable {
    let b = block.to_be_U32s();
    let mut s = RoundConstantsTable::new();
    for i in 0..K_SIZE {
        if i < 16 {
            s[i] = b[i];
        } else {
            let t16 = s[i - 16];
            let t15 = s[i - 15];
            let t7 = s[i - 7];
            let t2 = s[i - 2];
            let s1 = sigma(t2, 3, 0);
            let s0 = sigma(t15, 2, 0);
            s[i] = s1 + t7 + s0 + t16;
        }
    }
    s
}

pub fn shuffle(ws: RoundConstantsTable, hashi: Hash) -> Hash {
    let mut h = hashi;
    for i in 0..K_SIZE {
        let a0 = h[0];
        let b0 = h[1];
        let c0 = h[2];
        let d0 = h[3];
        let e0 = h[4];
        let f0 = h[5];
        let g0 = h[6];
        let h0: U32 = h[7];

// const HASH_INIT: Hash = Hash(secret_array!(
//     U32,
//     [
//         0x6a09e667u32,
//         0xbb67ae85u32,
//         0x3c6ef372u32,
//         0xa54ff53au32,
//         0x510e527fu32,
//         0x9b05688cu32,
//         0x1f83d9abu32,
//         0x5be0cd19u32
//     ]
// ));

// fn sigma(x: U32, i: usize, op: usize) -> U32 {
//     let mut tmp: U32 = x.rotate_right(OP_TABLE[3 * i + 2]);
//     if op == 0 {
//         tmp = x >> OP_TABLE[3 * i + 2]
//     }
//     x.rotate_right(OP_TABLE[3 * i]) ^ x.rotate_right(OP_TABLE[3 * i + 1]) ^ tmp
// }

pub fn compress(block: Block, h_in: Hash) -> Hash {
    let s = schedule(block);
    let mut h = shuffle(s, h_in);
    for i in 0..8 {
        h[i] = h[i] + h_in[i];
    }
    h
}

// fn shuffle(ws: RoundConstantsTable, hashi: Hash) -> Hash {
//     let mut h = hashi;
//     for i in 0..K_SIZE {
//         let a0 = h[0];
//         let b0 = h[1];
//         let c0 = h[2];
//         let d0 = h[3];
//         let e0 = h[4];
//         let f0 = h[5];
//         let g0 = h[6];
//         let h0: U32 = h[7];

//         let t1 = h0 + sigma(e0, 1, 1) + ch(e0, f0, g0) + K_TABLE[i] + ws[i];
//         let t2 = sigma(a0, 0, 1) + maj(a0, b0, c0);

//         h[0] = t1 + t2;
//         h[1] = a0;
//         h[2] = b0;
//         h[3] = c0;
//         h[4] = d0 + t1;
//         h[5] = e0;
//         h[6] = f0;
//         h[7] = g0;
//     }
//     h
// }

// fn compress(block: Block, h_in: Hash) -> Hash {
//     let s = schedule(block);
//     let mut h = shuffle(s, h_in);
//     for i in 0..8 {
//         h[i] = h[i] + h_in[i];
//     }
//     h
// }

// pub fn hash(msg: &ByteSeq) -> Sha256Digest {
//     let mut h = HASH_INIT;
//     // FIXME: #96 use exact_chunks
//     let mut last_block = Block::new();
//     let mut last_block_len = 0;
//     for i in 0..msg.num_chunks(BLOCK_SIZE) {
//         let (block_len, block) = msg.get_chunk(BLOCK_SIZE, i);
//         if block_len < BLOCK_SIZE {
//             last_block = Block::new().update_start(&block);
//             last_block_len = block_len;
//         } else {
//             let compress_input = Block::from_seq(&block);
//             h = compress(compress_input, h);
//         }
//     }

//     last_block[last_block_len] = U8(0x80u8);
//     let len_bist = U64((msg.len() * 8) as u64);
//     if last_block_len < BLOCK_SIZE - LEN_SIZE {
//         last_block = last_block.update(BLOCK_SIZE - LEN_SIZE, &U64_to_be_bytes(len_bist));
//         h = compress(last_block, h);
//     } else {
//         let mut pad_block = Block::new();
//         pad_block = pad_block.update(BLOCK_SIZE - LEN_SIZE, &U64_to_be_bytes(len_bist));
//         h = compress(last_block, h);
//         h = compress(pad_block, h);
//     }

//     Sha256Digest::from_seq(&h.to_be_bytes())
// }

// pub fn sha256(msg: &ByteSeq) -> Sha256Digest {
//     hash(msg)
// }
