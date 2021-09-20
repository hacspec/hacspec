pub type Res = (usize, usize);
pub enum ResTyp {
    Ok (Res),
    Err,
}

fn simpl(p : Res) -> Res {
    p
}

pub fn test_simpl_fails () -> bool {
    match ResTyp::Ok ((42,42)) {
	ResTyp::Ok (res) => simpl (res) == (42,42),
	ResTyp::Err => false,
    }
}
