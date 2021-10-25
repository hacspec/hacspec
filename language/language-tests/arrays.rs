use hacspec_lib::*;

array!(Block, 8, U32);

pub fn shuffle(b: Block) -> Block {
    let mut b = b;
    let tmp = b[0];
    b[0] = b[1];
    b[1] = tmp;
    b
}

pub fn linear_manipulations(a: Seq<u8>) -> Seq<u8> {
    let b = if true { a } else { a };
    let mut c = b.clone();
    if false {
        c = c.update_start(&b);
    } else {
        c = b;
    }
    c
}
