use hacspec_lib::*;

type MyIntegerType = usize;

pub fn foo(mut x: MyIntegerType) -> usize {
    for i in 0..x {
        x = i
    }
    x
}

type MyU32IntegerType = u32;

pub fn baz(mut x: MyU32IntegerType) -> MyU32IntegerType {
    for i in 0..(x as usize) {
        x = i as u32;
    }
    x
}

// https://github.com/hacspec/hacspec/issues/135
pub fn bar(x: U32) -> U32 {
    let mut y = x;
    for _ in 0..5 {
        y = y + U32(1u32)
    }
    y
}

pub fn foobar(x: u32) -> Result<u32, u32> {
    let mut y = x;
    for _ in 0..5 {
        if y > 100u32 {
            Result::<u32, u32>::Err(y)?;
        }
        
        y = y + 1u32
    }
    Result::<u32, u32>::Ok (y)
}
