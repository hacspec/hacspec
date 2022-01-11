use hacspec_lib::*;

pub fn foo_option(x: bool) -> Option<u64> {
    if x {
        Option::<u64>::Some(42u64)
    } else {
        Option::<u64>::None
    }
}

pub fn bar_option() -> Option<u64> {
    let x = foo_option(false)?;
    Option::<u64>::Some(x + 1u64)
}

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

pub fn fizzbazbaz() -> Result<u64, U8> {
    let mut x = foo(false)?;
    let mut y = foo(true)?;
    x = x + y;
    y = foo(false)?;
    Result::<u64, U8>::Ok(x + y)
}

pub fn fizzbazbazbar(mut s: Seq<u64>) -> Result<u64, U8> {
    let y = foo(false)?;
    s[0] = foo(true)?;
    Result::<u64, U8>::Ok(s[0] + y)
}

pub fn baz() -> Result<u32, U8> {
    let x = foo(false)?;
    let mut out = 0u32;
    if true || false {
        let _y = foo(true)?;
        foo(false || true)?;
    } else {
        foo(false && true)?;
        out = x as u32 + 1u32;
    }
    Result::<u32, U8>::Ok(out)
}

pub fn fizzbar() -> Result<u32, U8> {
    let _x = foo(false)?;
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

pub type alias = Result<u32, U8>;

pub fn alias_test() -> alias {
    if true {
        Result::<u32, U8>::Err(U8(0u8))?;
    }
    Result::<u32, U8>::Ok(1u32)
}
