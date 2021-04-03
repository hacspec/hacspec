use hacspec_lib::*;

array!(Block, 8, U32);

pub fn shuffle(b: Block) -> Block {
    let mut b = b;
    let tmp = b[0];
    b[0] += b[1];
    b[1] = tmp;
    b
}
