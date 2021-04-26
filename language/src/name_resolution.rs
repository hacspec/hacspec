use std::fmt;

use im::HashMap;

use crate::rustspec::*;
use std::sync::atomic::{AtomicUsize, Ordering};

pub static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_hacspec_id() -> usize {
    ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

pub(crate) fn to_fresh_ident(x: &String) -> Ident {
    Ident::Local(LocalIdent {
        id: fresh_hacspec_id(),
        name: x.clone(),
    })
}

#[derive(Debug, Clone)]
pub enum DictEntry {
    Alias,
    Array,
    NaturalInteger,
}

pub type NameContext = HashMap<String, Ident>;

#[derive(Clone)]
pub struct TopLevelContext {
    pub functions: HashMap<FnKey, FnValue>,
    pub consts: HashMap<TopLevelIdent, Spanned<BaseTyp>>,
    pub typ_dict: HashMap<TopLevelIdent, (Typ, DictEntry)>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum FnKey {
    Independent(TopLevelIdent),
    Impl(BaseTyp, TopLevelIdent),
}

impl fmt::Display for FnKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                FnKey::Independent(ident) => format!("{}", ident),
                FnKey::Impl(t, n) => format!("{}::{}", t, n),
            }
        )
    }
}

impl fmt::Debug for FnKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Debug)]
pub enum FnValue {
    Local(FuncSig),
    External(ExternalFuncSig),
    ExternalNotInHacspec(String),
}
