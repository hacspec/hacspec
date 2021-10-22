use hacspec_lib::*;

type MyIntegerType = usize;

pub fn foo(mut x: MyIntegerType) -> usize {
    for i in 0..x {
        x = i
    }
    x

// https://github.com/hacspec/hacspec/issues/135
pub fn foo(x: U32) -> U32 {
    let mut y = x;
    for _ in 0..5 {
        y = y + U32(1u32)
    }
    y
}
