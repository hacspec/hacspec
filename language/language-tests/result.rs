use hacspec_lib::*;

bytes!(SimpleOutput, 3);
type SimpleOutputResult = Result<SimpleOutput, u8>;

pub fn foo(x: Result<Result<U32, usize>, usize>) -> U32 {
    let _y = Result::<U32, usize>::Ok(U32(1u32));
    let _z = Result::<U32, usize>::Err(8);
    match x {
        Result::<Result<U32, usize>, usize>::Ok(_) => U32(0u32),
        Result::<Result<U32, usize>, usize>::Err(x) => U32(x as u32),
    }
}

fn other() -> Result<SimpleOutput, u8> {
    Result::<SimpleOutput, u8>::Err(1u8)
}

pub fn type_confusion() -> Result<SimpleOutput, u8> {
    other()
}

pub fn return_type_alias() -> Result<SimpleOutput, u8> {
    SimpleOutputResult::Err(1u8)
}
