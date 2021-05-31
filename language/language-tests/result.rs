use hacspec_lib::*;

pub fn foo(x: Result<Result<U32, usize>, usize>) -> U32 {
    let _y = Result::<U32, usize>::Ok(U32(1u32));
    let _z = Result::<U32, usize>::Err(8);
    match x {
        Result::<Result<U32, usize>, usize>::Ok(_) => U32(0u32),
        Result::<Result<U32, usize>, usize>::Err(x) => U32(x as u32),
    }
}
