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

pub fn creating_public_byte_seq() -> PublicSeq<u8> {
    public_byte_seq!(0u8, 1u8, 2u8, 3u8)
}

pub fn creating_byte_seq() -> Seq<U8> {
    byte_seq!(0u8, 1u8, 2u8, 3u8)
}
