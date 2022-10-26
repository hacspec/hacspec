pub type Res = (usize, usize);
pub enum ResTyp {
    Ok(Res),
}

pub fn test_simpl_fails() -> Res {
    match ResTyp::Ok((42, 42)) {
        ResTyp::Ok(res) => res,
    }
}

#[derive(Clone)]
pub struct MyTupleType(u16, u8);

pub fn test_tuple_destructuring() {
    let tuple = MyTupleType(1u16, 2u8).clone();
    let MyTupleType(_a, _b) = tuple;
}

// Test case for issue #228
pub fn unit_type() {
    if true {
        ()
    };
    ()
}

// Issue #287
pub struct EmptyTuple();
pub fn test_empty_tuple() -> EmptyTuple {
    EmptyTuple()
}
