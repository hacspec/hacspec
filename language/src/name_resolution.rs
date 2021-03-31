use std::fmt;

use im::HashMap;
use rustc_session::Session;

use crate::rustspec::*;
use crate::util::check_vec;
use crate::HacspecErrorEmitter;

#[derive(Debug, Clone)]
pub enum DictEntry {
    Alias,
    Array,
    NaturalInteger,
}

pub type ResolutionResult<T> = Result<T, ()>;

type NameContext = HashMap<String, Ident>;

#[derive(Clone)]
pub struct TopLevelContext {
    functions: HashMap<FnKey, FnValue>,
    consts: HashMap<String, Spanned<BaseTyp>>,
    typ_dict: HashMap<String, (Typ, DictEntry)>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum FnKey {
    Independent(Ident),
    Impl(BaseTyp, Ident),
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

fn resolve_item(
    sess: &Session,
    (i, i_span): Spanned<Item>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Item>> {
    match i {
        _ => Ok((i, i_span)),
    }
}

fn process_decl_item(
    sess: &Session,
    (i, i_span): &Spanned<Item>,
    top_level_context: &mut TopLevelContext,
) -> ResolutionResult<()> {
    match i {
        Item::ConstDecl(id, typ, _e) => {
            top_level_context.consts.insert(
                match id {
                    (Ident::Original(id), _) => id.clone(),
                    _ => panic!(), // should not happen
                },
                typ.clone(),
            );
            Ok(())
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = match &size.0 {
                Expression::Lit(Literal::Usize(u)) => ArraySize::Integer(u.clone()),
                Expression::Named(Ident::Original(s)) => ArraySize::Ident(s.clone()),
                _ => {
                    sess.span_rustspec_err(
                        size.1.clone(),
                        "expected identifier or integer literal",
                    );
                    return Err(());
                }
            };
            let _ = top_level_context.typ_dict.insert(
                match &id.0 {
                    Ident::Original(s) => s.clone(),
                    Ident::Hacspec(_, _) => panic!(),
                },
                (
                    (
                        (Borrowing::Consumed, id.1.clone()),
                        (
                            BaseTyp::Array((new_size, size.1.clone()), Box::new(cell_t.clone())),
                            id.1.clone(),
                        ),
                    ),
                    DictEntry::Array,
                ),
            );
            match index_typ {
                None => (),
                Some(index_typ) => {
                    top_level_context.typ_dict.insert(
                        match &index_typ.0 {
                            Ident::Original(s) => s.clone(),
                            Ident::Hacspec(_, _) => panic!(),
                        },
                        (
                            (
                                (Borrowing::Consumed, index_typ.1.clone()),
                                (BaseTyp::Usize, index_typ.1.clone()),
                            ),
                            DictEntry::Alias,
                        ),
                    );
                }
            };
            Ok(())
        }
        Item::FnDecl((f, _f_span), sig, _b) => {
            top_level_context
                .functions
                .insert(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
            Ok(())
        }
        _ => Ok(()),
    }
}

pub fn resolve_crate(sess: &Session, p: Program) -> ResolutionResult<(Program, TopLevelContext)> {
    let mut top_level_ctx = TopLevelContext {
        consts: HashMap::new(),
        functions: HashMap::new(),
        typ_dict: HashMap::new(),
    };
    // We do a first pass that collects types and signatures of top-level
    // items
    for item in p.items.iter() {
        process_decl_item(sess, item, &mut top_level_ctx)?;
    }
    Ok((
        Program {
            items: check_vec(
                p.items
                    .into_iter()
                    .map(|i| resolve_item(sess, i, &top_level_ctx))
                    .collect(),
            )?,
            imported_crates: p.imported_crates,
            ty_aliases: p.ty_aliases,
        },
        top_level_ctx,
    ))
}
