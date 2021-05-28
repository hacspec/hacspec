use hacspec_lib::*;

pub fn foo(x: Result<Result<U32, usize>, usize>) -> U32 {
    match x {
        Result::<Result<U32, usize>, usize>::Ok(_) => U32(0u32),
        Result::<Result<U32, usize>, usize>::Err(x) => U32(x as u32),
    }
}
