pub type Res = (usize, usize);
pub enum ResTyp {
    Ok (Res),
}

pub fn test_simpl_fails () -> Res {
    match ResTyp::Ok ((42,42)) {
	ResTyp::Ok (res) => res,
    }
}
