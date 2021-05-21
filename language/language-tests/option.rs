use hacspec_lib::*;

fn foo(x: Option<Option<U32>>) -> U32 {
    match x {
        Option::<Option<U32>>::None => U32(0u32),
        Option::<Option<U32>>::Some(x) => x.unwrap(),
    }
}
