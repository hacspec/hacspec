use im::HashMap;
use rustc_session::Session;

use crate::rustspec::*;
use crate::util::check_vec;

#[derive(Debug, Clone)]
pub enum DictEntry {
    Alias,
    Array,
    NaturalInteger,
}

pub type ResolutionResult<T> = Result<T, ()>;

pub type TypeDict = HashMap<String, (Typ, DictEntry)>;

type NameContext = HashMap<String, Ident>;

fn resolve_item(sess: &Session, (i, i_span): Spanned<Item>) -> ResolutionResult<Spanned<Item>> {
    match i {
        _ => Ok((i, i_span)),
    }
}

pub fn resolve_crate(sess: &Session, p: Program) -> ResolutionResult<(Program, TypeDict)> {
    let mut typ_dict = HashMap::new();
    Ok((
        Program {
            items: check_vec(p.items.into_iter().map(|i| resolve_item(sess, i)).collect())?,
            imported_crates: p.imported_crates,
            ty_aliases: p.ty_aliases,
        },
        typ_dict,
    ))
}
