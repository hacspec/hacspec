// Import hacspec and all needed definitions.
use hacspec::prelude::*;

pub enum Variant {
    // SHA224 = 224,
    SHA256 = 256,
    // SHA384 = 384,
    // SHA512 = 512,
}

const BLOCK_SIZE: usize = 64;
const LEN_SIZE: usize = 8;
pub const K_SIZE: usize = 64;
pub const HASH_SIZE: usize = Variant::SHA256 as usize / 8;

type WordT = U32;
bytes!(Block, BLOCK_SIZE);
bytes!(OpTableType, 12);
bytes!(Digest, HASH_SIZE);
array!(RoundConstantsTable, K_SIZE, U32);
// FIXME: for some reason we can't use WorT here.
array!(Hash, 8, U32);

fn ch(x: WordT, y: WordT, z: WordT) -> WordT {
    (x & y) ^ ((!x) & z)
}

fn maj(x: WordT, y: WordT, z: WordT) -> WordT {
    (x & y) ^ ((x & z) ^ (y & z))
}

fn sigma(x: WordT, i: usize, op: usize) -> WordT {
    let op_table = OpTableType::from([2u8, 13, 22, 6, 11, 25, 7, 18, 3, 17, 19, 10]);
    let tmp: WordT = if op == 0 {
        x >> op_table[3 * i + 2].into()
    } else {
        x.rotate_right(op_table[3 * i + 2].into())
    };
    x.rotate_right(op_table[3 * i].into()) ^ x.rotate_right(op_table[3 * i + 1].into()) ^ tmp
}

fn schedule(block: Block) -> RoundConstantsTable {
    let b = block.to_U32s_be();
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

fn shuffle(ws: RoundConstantsTable, hashi: Hash) -> Hash {
    let k_table = RoundConstantsTable::from([
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ]);

    let mut h = hashi;
    for i in 0..K_SIZE {
        let a0 = h[0];
        let b0 = h[1];
        let c0 = h[2];
        let d0 = h[3];
        let e0 = h[4];
        let f0 = h[5];
        let g0 = h[6];
        let h0: WordT = h[7];

        let t1 = h0 + sigma(e0, 1, 1) + ch(e0, f0, g0) + k_table[i] + ws[i];
        let t2 = sigma(a0, 0, 1) + maj(a0, b0, c0);

        h[0] = t1 + t2;
        h[1] = a0;
        h[2] = b0;
        h[3] = c0;
        h[4] = d0 + t1;
        h[5] = e0;
        h[6] = f0;
        h[7] = g0;
    }
    h
}

fn compress(block: Block, h_in: Hash) -> Hash {
    let s = schedule(block);
    let mut h = shuffle(s, h_in);
    for i in 0..8 {
        h[i] += h_in[i];
    }
    h
}

pub fn hash(msg: ByteSeq) -> Digest {
    let mut h = Hash::from([
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ]);
    for (block_len, block) in msg.chunks(BLOCK_SIZE) {
        if block_len < BLOCK_SIZE {
            // Add padding for last block
            let mut last_block = Block::new();
            last_block = last_block.update(0, Block::from(block));
            last_block[block_len] = U8(0x80);
            let len_bist: U64 = (msg.len() * 8).into();
            if block_len < BLOCK_SIZE - LEN_SIZE {
                last_block = last_block.update(BLOCK_SIZE - LEN_SIZE, u64_to_be_bytes(len_bist));
                h = compress(last_block, h);
            } else {
                let mut pad_block = Block::new();
                pad_block = pad_block.update(BLOCK_SIZE - LEN_SIZE, u64_to_be_bytes(len_bist));
                h = compress(last_block, h);
                h = compress(pad_block, h);
            }
        } else {
            h = compress(block.into(), h);
        }
    }

    Digest::from(&h.to_bytes_be()[..])
}
