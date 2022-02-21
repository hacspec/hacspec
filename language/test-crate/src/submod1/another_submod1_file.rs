use crate::*;

pub enum ResTyp {
    Ok(Res),
}

pub fn some_other_fun() -> Result<(), Error> {
    Result::<(), Error>::Err(Error::First)
}
