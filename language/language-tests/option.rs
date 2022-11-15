use hacspec_lib::*;

pub fn foo(x: Option<Option<U32>>) -> U32 {
    let y = Option::<U32>::None;
    let _z = Option::<Option<U32>>::Some(y);
    match x {
        Option::<Option<U32>>::None => U32(0u32),
        Option::<Option<U32>>::Some(x) => x.unwrap(),
    }
}

pub fn foo_unannonated(x: Option<Option<U32>>) -> Option<U32> {
    let _y: Option<U32> = None;
    match x {
        None => Some(U32(0u32)),
        Some(None) => Some(U32(1u32)),
        Some(Some(x)) => Some(x),
    }
}
