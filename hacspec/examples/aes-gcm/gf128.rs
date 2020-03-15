// Import hacspec and all needed definitions.
use hacspec::prelude::*;

// Get Key, Block, and BLOCKSIZE types
// use crate::aes::{Key, Block};

const BLOCKSIZE: usize = 16;
// TODO: these should all cast to each other without into
bytes!(Block, BLOCKSIZE);
bytes!(Key, BLOCKSIZE);
bytes!(Tag, BLOCKSIZE);

// TODO: Use a 128-bit uint_n instead?
type Element = U128;
const IRRED: Element = U128(0xE100_0000_0000_0000_0000_0000_0000_0000);

fn fadd(x: Element, y: Element) -> Element {
    x ^ y
}

fn fmul(x: Element, y: Element) -> Element {
    let mut res: Element = U128(0);
    let mut sh = x;
    for i in 0..128 {
        if (y & (U128(1) << (127 - i))).declassify() != U128(0).declassify() {
            res ^= sh;
        }
        if (sh & U128(1)).declassify() != U128(0).declassify() {
            sh = (sh >> 1) ^ IRRED;
        } else {
            sh >>= 1;
        }
    }
    res
}

// GMAC

// TODO: block is actually subblock
fn encode(block: Block) -> Element {
    u128_from_be_bytes(U128Word::copy(block))
}

fn decode(e: Element) -> Block {
    Block::copy(u128_to_be_bytes(e))
}

// TODO: block is actually subblock
fn update(r: Element, block: Block, acc: Element) -> Element {
    fmul(fadd(encode(block), acc), r)
}

fn poly(msg: ByteSeq, r: Element) -> Element {
    let l = msg.len();
    let n_blocks: usize = l / BLOCKSIZE;
    let rem = l % BLOCKSIZE;
    let mut acc = U128(0);
    for i in 0..n_blocks {
        let k = i * BLOCKSIZE;
        acc = update(r, Block::from_sub_pad(msg.clone(), k..k + BLOCKSIZE), acc);
    }
    if rem != 0 {
        let k = n_blocks * BLOCKSIZE;
        let mut last_block = Block::new();
        last_block = last_block.update_sub(0, msg.clone(), k, rem);
        acc = update(r, last_block, acc);
    }
    acc
}

pub fn gmac(text: ByteSeq, k: Key) -> Tag {
    let s = Block::new();
    let r = encode(Block::copy(k));
    let a = poly(text, r);
    Tag::copy(decode(fadd(a, encode(s))))
}
