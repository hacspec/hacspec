mod submod1;
mod submod2;
pub use submod1::*;
pub use submod2::*;

pub fn test_simpl_fails() -> Res {
    match ResTyp::Ok((42, 42)) {
        ResTyp::Ok(res) => res,
    }
}

pub fn test_tuple_destructuring() {
    let tuple = MyTupleType(1u16, 2u8).clone();
    let MyTupleType(_a, _b) = tuple;
}

pub fn some_fun() -> Result<(), Error> {
    Result::<(), Error>::Err(Error::First)
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let mut result = 2;
        result += 2;
        assert_eq!(result, 4);
    }
}
