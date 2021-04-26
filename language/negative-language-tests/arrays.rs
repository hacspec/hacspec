use hacspec_lib::*;

array!(Block, 8, U32);

pub fn shuffle(b: Block) -> Block {
    let mut b = b;
    let b1: U32 = b[1];
    b[0] += b1;
    b
}
