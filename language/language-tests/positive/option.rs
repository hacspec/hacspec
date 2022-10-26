use hacspec_lib::*;

pub fn foo(x: Option<Option<U32>>) -> U32 {
    let y = Option::<U32>::None;
    let _z = Option::<Option<U32>>::Some(y);
    match x {
        Option::<Option<U32>>::None => U32(0u32),
        Option::<Option<U32>>::Some(x) => x.unwrap(),
    }
}
