use hacspec_lib::*;

bytes!(SimpleOutput, 3);
type SimpleOutputResult = Result<SimpleOutput, u8>;

type SResult = SimpleOutputResult;

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

fn other_result_alias() -> SimpleOutputResult {
    Result::<SimpleOutput, u8>::Err(1u8)
}

pub fn type_confusion() -> Result<SimpleOutput, u8> {
    other()
}

pub fn return_type_alias() -> Result<SimpleOutput, u8> {
    SimpleOutputResult::Err(1u8)
}

pub fn type_alias_question_mark() -> Result<SimpleOutput, u8> {
    let _other_result = other_result_alias()?;
    SimpleOutputResult::Err(1u8)
}

pub fn type_alias_question_mark_return() -> SimpleOutputResult {
    let _other_result = other()?;
    SimpleOutputResult::Err(1u8)
}

pub fn type_double_alias_question_mark_return() -> SResult {
    let _other_result = other()?;
    SResult::Err(1u8)
}

pub fn unwrap_result() -> SimpleOutput {
    other().unwrap()
}

pub fn match_result() -> SimpleOutput {
    let result_value = type_double_alias_question_mark_return();
    match result_value {
        SResult::Ok(r) => r,
        SResult::Err(_) => SimpleOutput::new(),
    }
}
