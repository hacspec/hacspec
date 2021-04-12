use std::fmt;

use im::HashMap;
use rustc_session::Session;

use crate::rustspec::*;
use crate::util::check_vec;
use crate::HacspecErrorEmitter;
use rustc_span::DUMMY_SP;
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

pub type ResolutionResult<T> = Result<T, ()>;

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

fn resolve_item(
    _sess: &Session,
    (i, i_span): Spanned<Item>,
    _top_level_ctx: &TopLevelContext,
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
            top_level_context.consts.insert(id.0.clone(), typ.clone());
            Ok(())
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = match &size.0 {
                Expression::Lit(Literal::Usize(u)) => ArraySize::Integer(u.clone()),
                Expression::Named(Ident::Unresolved(s)) => {
                    ArraySize::Ident(TopLevelIdent(s.clone()))
                }
                _ => {
                    sess.span_rustspec_err(
                        size.1.clone(),
                        "expected identifier or integer literal",
                    );
                    return Err(());
                }
            };
            top_level_context.typ_dict.insert(
                id.0.clone(),
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
                        index_typ.0.clone(),
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
        Item::NaturalIntegerDecl(typ_ident, canvas_typ_ident, secrecy, canvas_size, mod_string) => {
            process_decl_item(
                sess,
                &(
                    Item::ArrayDecl(
                        canvas_typ_ident.clone(),
                        canvas_size.clone(),
                        match secrecy {
                            Secrecy::Secret => (
                                BaseTyp::Named(
                                    (TopLevelIdent("U8".to_string()), canvas_typ_ident.1.clone()),
                                    None,
                                ),
                                canvas_typ_ident.1.clone(),
                            ),
                            Secrecy::Public => (BaseTyp::UInt8, canvas_typ_ident.1.clone()),
                        },
                        None,
                    ),
                    *i_span,
                ),
                top_level_context,
            )?;
            top_level_context.typ_dict.insert(
                typ_ident.0.clone() ,
                (
                    (
                        (Borrowing::Consumed, (typ_ident.1).clone()),
                        (
                            BaseTyp::NaturalInteger(
                                secrecy.clone(),
                                mod_string.clone(),
                                match &canvas_size.0 {
                                    Expression::Lit(Literal::Usize(size)) => {
                                        (size.clone(), (canvas_size.1).clone())
                                    }
                                    _ => {
                                        sess.span_rustspec_err(
                                            (canvas_size.1).clone(), "the size of the natural integer encoding has to be a usize literal"
                                        );
                                        return Err(())
                                    }
                                },
                            ),
                            typ_ident.1.clone(),
                        ),
                    ),
                    DictEntry::NaturalInteger,
                ),
            );
            Ok(())
        }
        Item::SimplifiedNaturalIntegerDecl(typ_ident, secrecy, canvas_size) => {
            top_level_context.typ_dict.insert(
                typ_ident.0.clone(),
                match &canvas_size.0 {
                    Expression::Lit(Literal::Usize(size)) => (
                        (
                            (Borrowing::Consumed, (typ_ident.1).clone()),
                            (
                                BaseTyp::NaturalInteger(
                                    secrecy.clone(),
                                    (String::new(), DUMMY_SP), // TODO: replace with real modulo value
                                    // For now we can leave this empty because
                                    // We don't use it in the typechecker
                                    (size.clone(), (canvas_size.1).clone()),
                                ),
                                typ_ident.1.clone(),
                            ),
                        ),
                        DictEntry::NaturalInteger,
                    ),
                    _ => {
                        sess.span_rustspec_err(
                            (canvas_size.1).clone(),
                            "the size of the natural integer encoding has to be a usize literal",
                        );
                        return Err(());
                    }
                },
            );
            Ok(())
        }
        Item::FnDecl((f, _f_span), sig, _b) => {
            top_level_context
                .functions
                .insert(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
            Ok(())
        }
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
