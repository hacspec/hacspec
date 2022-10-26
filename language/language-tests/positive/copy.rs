use hacspec_lib::*;

#[derive(Clone, Copy)]
pub struct MyStruct(usize);

fn other(x: MyStruct) -> MyStruct {
    x
}

pub fn first() -> MyStruct {
    let s = MyStruct(0);
    // Consuming s or rather copying it.
    let s_copy = other(s);
    // Deconstructing s (copying again).
    let MyStruct(s_copy2) = s;
    // Without the copy trait `s` is consumed here.
    other(s)
}
