use hacspec_lib::*;

pub fn foo(x: bool) -> Result<u64, U8> {
    if x {
        Result::<u64, U8>::Ok(42u64)
    } else {
        Result::<u64, U8>::Err(U8(0u8))
    }
}

pub fn bar() -> Result<u64, U8> {
    let x = foo(false)?;
    Result::<u64, U8>::Ok(x + 1u64)
}

pub fn fizzbaz() -> Result<u64, U8> {
    let x = foo(false)?;
    let y = foo(true)?;
    Result::<u64, U8>::Ok(x + y)
}

pub fn baz() -> Result<u32, U8> {
    let x = foo(false)?;
    let mut out = 0u32;
    if true || false {
        let y = foo(true)?;
        out = y as u32 + 1u32;
        foo(false || true)?;
    } else {
        foo(false && true)?;
        out = x as u32 + 1u32;
    }
    Result::<u32, U8>::Ok(out)
}

pub fn fizzbar() -> Result<u32, U8> {
    let x = foo(false)?;
    let mut out = 0u32;
    for i in 0..200 {
        let y = foo(true)?;
        out = i as u32 + y as u32 + out;
    }
    Result::<u32, U8>::Ok(out)
}

pub fn fizzbarbuzz() -> Result<u32, U8> {
    let x = foo(false)?;
    let mut out = 0u32;
    for i in 0..200 {
        if true || false {
            let y = foo(true)?;
            out = y as u32 + out;
            foo(false || true)?;
        } else {
            foo(false && true)?;
            out = x as u32 + i as u32;
        }
    }
    Result::<u32, U8>::Ok(out)
}
