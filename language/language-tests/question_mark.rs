use hacspec_lib::*;

pub fn foo(x: bool) -> Result<u32, U8> {
    if x {
        Result::<u32, U8>::Ok(42u32)
    } else {
        Result::<u32, U8>::Err(U8(0u8))
    }
}

pub fn bar() -> Result<u32, U8> {
    let x = foo(false)?;
    Result::<u32, U8>::Ok(x + 1u32)
}
