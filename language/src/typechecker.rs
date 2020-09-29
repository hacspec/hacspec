use crate::rustspec::*;
use crate::HacspectErrorEmitter;

use hacspec_sig;
use im::{HashMap, HashSet};
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;
use rustc_span::{Span, DUMMY_SP};
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

// TODO: explain that we need typechecking inference to disambiguate method calls

pub static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_rustspec_id() -> HacspecId {
    HacspecId(ID_COUNTER.fetch_add(1, Ordering::SeqCst))
}

fn fresh_ident(x: &Ident) -> Ident {
    match x {
        Ident::Hacspec(_, _) => panic!("fresh_ident only replaces original Rust ident ids"),
        Ident::Original(n) => Ident::Hacspec(fresh_rustspec_id(), n.clone()),
    }
}

fn is_numeric(t: &Typ, typ_dict: &TypeDict) -> bool {
    if (t.0).0 == Borrowing::Borrowed {
        return false;
    };
    match &(t.1).0 {
        BaseTyp::UInt128 => true,
        BaseTyp::Int128 => true,
        BaseTyp::UInt64 => true,
        BaseTyp::Int64 => true,
        BaseTyp::UInt32 => true,
        BaseTyp::Int32 => true,
        BaseTyp::UInt16 => true,
        BaseTyp::Int16 => true,
        BaseTyp::UInt8 => true,
        BaseTyp::Int8 => true,
        BaseTyp::Usize => true,
        BaseTyp::Isize => true,
        BaseTyp::Named((Ident::Original(name), _), None) => match typ_dict.get(name) {
            Some((new_t1, dict_entry)) => {
                assert!((new_t1.0).0 == Borrowing::Consumed);
                match dict_entry {
                    DictEntry::Alias => is_numeric(new_t1, typ_dict),
                    DictEntry::Array | DictEntry::NaturalInteger => true,
                }
            }
            None => match name.as_str() {
                "U8" | "U16" | "U32" | "U64" | "U128" | "I8" | "I16" | "I32" | "I64" | "I128" => {
                    true
                }
                _ => false,
            },
        },
        BaseTyp::Array(_, _) => true,
        _ => false,
    }
}

fn is_copy(t: &BaseTyp, typ_dict: &TypeDict) -> bool {
    match t {
        BaseTyp::Unit => true,
        BaseTyp::Bool => true,
        BaseTyp::UInt128 => true,
        BaseTyp::Int128 => true,
        BaseTyp::UInt64 => true,
        BaseTyp::Int64 => true,
        BaseTyp::UInt32 => true,
        BaseTyp::Int32 => true,
        BaseTyp::UInt16 => true,
        BaseTyp::Int16 => true,
        BaseTyp::UInt8 => true,
        BaseTyp::Int8 => true,
        BaseTyp::Usize => true,
        BaseTyp::Isize => true,
        BaseTyp::Seq(_) => false,
        BaseTyp::Str => false,
        BaseTyp::Array(_, _) => true,
        BaseTyp::Named((Ident::Original(name), _), arg) => match typ_dict.get(name) {
            Some((new_t1, dict_entry)) => {
                debug_assert!((new_t1.0).0 == Borrowing::Consumed);
                match dict_entry {
                    DictEntry::Alias => is_copy(&(new_t1.1).0, typ_dict),
                    DictEntry::Array | DictEntry::NaturalInteger => true,
                }
            }
            None => match arg {
                None => match name.as_str() {
                    "U8" | "U16" | "U32" | "U64" | "U128" | "I8" | "I16" | "I32" | "I64"
                    | "I128" => true,
                    _ => false,
                },
                Some(_) => false,
            },
        },
        BaseTyp::Named((Ident::Hacspec(_, _), _), _) => panic!(), // should not happen
        BaseTyp::Variable(_) => false,
        BaseTyp::Tuple(ts) => ts.iter().all(|(t, _)| is_copy(t, typ_dict)),
        BaseTyp::NaturalInteger(_, _) => true,
    }
}

fn is_array(
    sess: &Session,
    t: &Typ,
    typ_dict: &TypeDict,
    span: &Span,
) -> Result<(Option<Spanned<ArraySize>>, Spanned<BaseTyp>), ()> {
    match &(t.1).0 {
        BaseTyp::Seq(t1) => Ok((None, t1.as_ref().clone())),
        BaseTyp::Named(id, None) => match &id.0 {
            Ident::Hacspec(_, _) => panic!(),
            Ident::Original(name) => match typ_dict.get(name) {
                Some((new_t, dict_entry)) => match dict_entry {
                    DictEntry::Alias => is_array(sess, new_t, typ_dict, span),
                    DictEntry::Array => {
                        match &(new_t.1).0 {
                            BaseTyp::Array(size, cell_t) => {
                                Ok((Some(size.clone()), cell_t.as_ref().clone()))
                            }
                            _ => panic!(), // shouldd not happen
                        }
                    }
                    DictEntry::NaturalInteger => {
                        sess.span_rustspec_err(
                            span.clone(),
                            format!(
                                "expected an array but got a natural integer type: {}{}",
                                &(t.0).0,
                                &(t.1).0
                            )
                            .as_str(),
                        );
                        Err(())
                    }
                },
                None => {
                    sess.span_rustspec_err(
                        span.clone(),
                        format!("expected an array but got type {}{}", &(t.0).0, &(t.1).0).as_str(),
                    );
                    Err(())
                }
            },
        },
        BaseTyp::Named(_, Some(_)) => Err(()),
        BaseTyp::Array(len, cell_t) => Ok((Some(len.clone()), cell_t.as_ref().clone())),
        _ => {
            sess.span_rustspec_err(
                span.clone(),
                format!("expected an array but got type {}{}", &(t.0).0, &(t.1).0).as_str(),
            );
            Err(())
        }
    }
}

fn is_index(t: &BaseTyp) -> bool {
    match t {
        BaseTyp::UInt128 => true,
        BaseTyp::Int128 => true,
        BaseTyp::UInt64 => true,
        BaseTyp::Int64 => true,
        BaseTyp::UInt32 => true,
        BaseTyp::Int32 => true,
        BaseTyp::UInt16 => true,
        BaseTyp::Int16 => true,
        BaseTyp::UInt8 => true,
        BaseTyp::Int8 => true,
        BaseTyp::Usize => true,
        BaseTyp::Isize => true,
        _ => false,
    }
}

fn is_castable_integer(t: &BaseTyp) -> bool {
    match t {
        BaseTyp::UInt128 => true,
        BaseTyp::Int128 => true,
        BaseTyp::UInt64 => true,
        BaseTyp::Int64 => true,
        BaseTyp::UInt32 => true,
        BaseTyp::Int32 => true,
        BaseTyp::UInt16 => true,
        BaseTyp::Int16 => true,
        BaseTyp::UInt8 => true,
        BaseTyp::Int8 => true,
        BaseTyp::Usize => true,
        BaseTyp::Isize => true,
        _ => false,
    }
}

fn is_safe_casting(t1: &BaseTyp, t2: &BaseTyp) -> bool {
    match (t2, t1) {
        (BaseTyp::UInt128, BaseTyp::UInt64)
        | (BaseTyp::UInt128, BaseTyp::UInt32)
        | (BaseTyp::UInt128, BaseTyp::UInt16)
        | (BaseTyp::UInt128, BaseTyp::Usize)
        | (BaseTyp::UInt128, BaseTyp::UInt8) => true,
        (BaseTyp::UInt64, BaseTyp::UInt32)
        | (BaseTyp::UInt64, BaseTyp::UInt16)
        | (BaseTyp::UInt64, BaseTyp::Usize)
        | (BaseTyp::UInt64, BaseTyp::UInt8) => true,
        (BaseTyp::UInt32, BaseTyp::UInt16)
        | (BaseTyp::UInt32, BaseTyp::Usize)
        | (BaseTyp::UInt32, BaseTyp::UInt8) => true,
        (BaseTyp::UInt16, BaseTyp::UInt8) | (BaseTyp::UInt16, BaseTyp::Usize) => true,
        (BaseTyp::Int128, BaseTyp::Int64)
        | (BaseTyp::Int128, BaseTyp::Int32)
        | (BaseTyp::Int128, BaseTyp::Int16)
        | (BaseTyp::Int128, BaseTyp::Isize)
        | (BaseTyp::Int128, BaseTyp::Int8) => true,
        (BaseTyp::Int64, BaseTyp::Int32)
        | (BaseTyp::Int64, BaseTyp::Int16)
        | (BaseTyp::Int64, BaseTyp::Isize)
        | (BaseTyp::Int64, BaseTyp::Int8) => true,
        (BaseTyp::Int32, BaseTyp::Int16)
        | (BaseTyp::Int32, BaseTyp::Isize)
        | (BaseTyp::Int32, BaseTyp::Int8) => true,
        (BaseTyp::Int16, BaseTyp::Int8) | (BaseTyp::Int16, BaseTyp::Isize) => true,
        _ => false,
    }
}

type TypeVarCtx = HashMap<HacspecId, BaseTyp>;

fn unify_types(
    sess: &Session,
    t1: &Typ,
    t2: &Typ,
    typ_ctx: &TypeVarCtx,
    typ_dict: &TypeDict,
) -> TypecheckingResult<Option<TypeVarCtx>> {
    // We first have to remove all the aliases
    // We don't support generic aliases for now
    match &(t1.1).0 {
        BaseTyp::Named((Ident::Original(name1), _), None) => match typ_dict.get(name1) {
            Some(((new_t1_borrow, new_t1), DictEntry::Alias)) => {
                let new_new_t1_borrow = match (&(t1.0).0, &new_t1_borrow.0) {
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_rustspec_err(
                            (t1.0).1.clone(),
                            "double borrowing is forbidden in Hacspec!",
                        );
                        return Err(());
                    }
                    (Borrowing::Consumed, Borrowing::Borrowed)
                    | (Borrowing::Borrowed, Borrowing::Consumed) => {
                        (Borrowing::Borrowed, (t1.0).1.clone())
                    }
                    _ => (Borrowing::Consumed, (t1.0).1.clone()),
                };
                return unify_types(
                    sess,
                    &(new_new_t1_borrow, new_t1.clone()),
                    t2,
                    typ_ctx,
                    typ_dict,
                );
            }
            _ => (),
        },
        _ => (),
    }
    //Same thing for t2
    match &(t2.1).0 {
        BaseTyp::Named((Ident::Original(name2), _), None) => match typ_dict.get(name2) {
            Some(((new_t2_borrow, new_t2), DictEntry::Alias)) => {
                let new_new_t2_borrow = match (&(t2.0).0, &new_t2_borrow.0) {
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_rustspec_err(
                            (t2.0).1.clone(),
                            "double borrowing is forbidden in Hacspec!",
                        );
                        return Err(());
                    }
                    (Borrowing::Consumed, Borrowing::Borrowed)
                    | (Borrowing::Borrowed, Borrowing::Consumed) => {
                        (Borrowing::Borrowed, (t2.0).1.clone())
                    }
                    _ => (Borrowing::Consumed, (t2.0).1.clone()),
                };
                return unify_types(
                    sess,
                    t1,
                    &(new_new_t2_borrow, new_t2.clone()),
                    typ_ctx,
                    typ_dict,
                );
            }
            _ => (),
        },
        _ => (),
    }
    match (&(t1.0).0, &(t2.0).0) {
        (Borrowing::Consumed, Borrowing::Consumed) | (Borrowing::Borrowed, Borrowing::Borrowed) => {
            match (&(t1.1).0, &(t2.1).0) {
                (BaseTyp::Unit, BaseTyp::Unit) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Bool, BaseTyp::Bool) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::UInt128, BaseTyp::UInt128) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Int128, BaseTyp::Int128) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::UInt64, BaseTyp::UInt64) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Int64, BaseTyp::Int64) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::UInt32, BaseTyp::UInt32) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Int32, BaseTyp::Int32) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::UInt16, BaseTyp::UInt16) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Int16, BaseTyp::Int16) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::UInt8, BaseTyp::UInt8) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Int8, BaseTyp::Int8) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Usize, BaseTyp::Usize) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Isize, BaseTyp::Isize) => Ok(Some(typ_ctx.clone())),
                (BaseTyp::Seq(tc1), BaseTyp::Seq(tc2)) => unify_types(
                    sess,
                    &(((Borrowing::Consumed, (t1.1).1)), *tc1.clone()),
                    &(((Borrowing::Consumed, (t2.1).1)), *tc2.clone()),
                    typ_ctx,
                    typ_dict,
                ),
                (BaseTyp::Named(name1, args1), BaseTyp::Named(name2, args2)) => {
                    let (name1, name2) = match (&name1.0, &name2.0) {
                        (Ident::Original(name1), Ident::Original(name2)) => {
                            (name1.clone(), name2.clone())
                        }
                        _ => panic!(),
                    };
                    if name1 == name2 {
                        match (args1, args2) {
                            (None, None) => Ok(Some(typ_ctx.clone())),
                            (Some(args1), Some(args2)) => {
                                if args1.len() == args2.len() {
                                    args1.iter().zip(args2.iter()).fold(
                                        Ok(Some(typ_ctx.clone())),
                                        |typ_ctx, (arg1, arg2)| match typ_ctx? {
                                            None => Ok(None),
                                            Some(typ_ctx) => unify_types(
                                                sess,
                                                &(((Borrowing::Consumed, arg1.1)), arg1.clone()),
                                                &(((Borrowing::Consumed, arg2.1)), arg2.clone()),
                                                &typ_ctx,
                                                typ_dict,
                                            ),
                                        },
                                    )
                                } else {
                                    Ok(None)
                                }
                            }
                            _ => Ok(None),
                        }
                    } else {
                        Ok(None)
                    }
                }
                (BaseTyp::Tuple(ts1), BaseTyp::Tuple(ts2)) => {
                    if ts1.len() == ts2.len() {
                        ts1.iter().zip(ts2.iter()).fold(
                            Ok(Some(typ_ctx.clone())),
                            |typ_ctx, (tc1, tc2)| {
                                typ_ctx?.map_or(Ok(None), |typ_ctx| {
                                    unify_types(
                                        sess,
                                        &(((Borrowing::Consumed, (t1.1).1)), tc1.clone()),
                                        &(((Borrowing::Consumed, (t2.1).1)), tc2.clone()),
                                        &typ_ctx,
                                        typ_dict,
                                    )
                                })
                            },
                        )
                    } else {
                        Ok(None)
                    }
                }
                (BaseTyp::Variable(_), BaseTyp::Variable(_)) => Ok(None),
                (BaseTyp::Variable(id1), bt2) => Ok(Some(typ_ctx.update(id1.clone(), bt2.clone()))),
                (bt1, BaseTyp::Variable(id2)) => Ok(Some(typ_ctx.update(id2.clone(), bt1.clone()))),
                _ => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

fn bind_variable_type(
    sess: &Session,
    ty: &Spanned<BaseTyp>,
    typ_ctx: &TypeVarCtx,
) -> TypecheckingResult<BaseTyp> {
    match &ty.0 {
        BaseTyp::Variable(id) => match typ_ctx.get(&id) {
            None => {
                sess.span_rustspec_err(
                    ty.1.clone(),
                    format!("type {} cannot be unified, internal Hacspec error", ty.0).as_str(),
                );
                Err(())
            }
            Some(new_ty) => Ok(new_ty.clone()),
        },
        BaseTyp::Seq(arg_ty) => Ok(BaseTyp::Seq(Box::new((
            bind_variable_type(sess, arg_ty.as_ref(), typ_ctx)?,
            arg_ty.as_ref().1.clone(),
        )))),
        BaseTyp::Named(name, args) => Ok(BaseTyp::Named(
            name.clone(),
            match args
                .as_ref()
                .map::<Result<_, ()>, _>(|args: &Vec<Spanned<BaseTyp>>| {
                    check_vec(
                        args.iter()
                            .map(|arg| {
                                let new_ty: BaseTyp = bind_variable_type(sess, arg, typ_ctx)?;
                                Ok((new_ty, arg.1.clone()))
                            })
                            .collect(),
                    )
                }) {
                None => None,
                Some(Ok(x)) => Some(x),
                Some(Err(_)) => return Err(()),
            },
        )),
        BaseTyp::Tuple(args) => Ok(BaseTyp::Tuple(check_vec(
            args.iter()
                .map(|(arg, span)| {
                    Ok((
                        bind_variable_type(sess, &(arg.clone(), ty.1.clone()), typ_ctx)?,
                        span.clone(),
                    ))
                })
                .collect(),
        )?)),
        _ => Ok(ty.0.clone()),
    }
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

fn sig_args(sig: &FnValue) -> Vec<Typ> {
    match sig {
        FnValue::Local(sig) => sig.args.clone().into_iter().map(|(_, (x, _))| x).collect(),
        FnValue::External(sig) => sig.args.clone(),
        FnValue::ExternalNotInHacspec(_) => panic!(),
    }
}

fn sig_ret(sig: &FnValue) -> BaseTyp {
    match sig {
        FnValue::Local(sig) => sig.ret.0.clone(),
        FnValue::External(sig) => sig.ret.clone(),
        FnValue::ExternalNotInHacspec(_) => panic!(),
    }
}

#[derive(Clone)]
struct TopLevelContext {
    functions: HashMap<FnKey, FnValue>,
    consts: HashMap<String, (Spanned<BaseTyp>, Spanned<Expression>)>,
}

type VarContext = HashMap<HacspecId, (Typ, String)>;

#[derive(Debug, Clone)]
pub enum DictEntry {
    Alias,
    Array,
    NaturalInteger,
}

pub type TypeDict = HashMap<String, (Typ, DictEntry)>;

type NameContext = HashMap<String, Ident>;

type AllowedSigs = std::collections::HashSet<hacspec_sig::Signature>;

fn find_func(
    sess: &Session,
    key1: &FnKey,
    top_level_context: &TopLevelContext,
    typ_dict: &TypeDict,
    span: &Span,
) -> TypecheckingResult<(FnValue, TypeVarCtx)> {
    let candidates = top_level_context.functions.clone();
    let mut has_err = false;
    let candidates: Vec<_> = candidates
        .iter()
        .filter_map(|(key2, sig)| match (key1, key2) {
            (FnKey::Independent(n1), FnKey::Independent(n2)) => match (n1, n2) {
                (Ident::Original(n1), Ident::Original(n2)) => {
                    if n1 == n2 {
                        Some((HashMap::new(), sig))
                    } else {
                        None
                    }
                }
                _ => panic!(),
            },
            (FnKey::Impl(t1, n1), FnKey::Impl(t2, n2)) => {
                let t1 = match t1 {
                    BaseTyp::Named((Ident::Original(name), _), None) => typ_dict.get(name).map_or(
                        (
                            (Borrowing::Consumed, span.clone()),
                            (t1.clone(), span.clone()),
                        ),
                        |(t_alias, entry_typ)| match entry_typ {
                            DictEntry::Alias => t_alias.clone(),
                            DictEntry::Array | DictEntry::NaturalInteger => (
                                (Borrowing::Consumed, span.clone()),
                                (t1.clone(), span.clone()),
                            ),
                        },
                    ),
                    _ => (
                        (Borrowing::Consumed, span.clone()),
                        (t1.clone(), span.clone()),
                    ),
                };
                let unification: TypecheckingResult<Option<TypeVarCtx>> = unify_types(
                    sess,
                    &t1,
                    &(
                        (Borrowing::Consumed, span.clone()),
                        (t2.clone(), span.clone()),
                    ),
                    &HashMap::new(),
                    typ_dict,
                );
                match unification {
                    Ok(Some(new_typ_ctx)) => match (n1, n2) {
                        (Ident::Original(n1), Ident::Original(n2)) => {
                            if n1 == n2 {
                                Some((new_typ_ctx, sig))
                            } else {
                                None
                            }
                        }
                        _ => panic!(),
                    },

                    Ok(None) => None,
                    Err(_) => {
                        has_err = true;
                        None
                    }
                }
            }
            _ => None,
        })
        .collect();
    if has_err {
        return Err(());
    }
    if candidates.len() == 0 {
        sess.span_rustspec_err(*span, format!("function {} cannot be found", key1).as_str());
        return Err(());
    }
    // If there are multiple candidates we just take the first one
    for (typ_ctx, sig) in candidates {
        return Ok((sig.clone(), typ_ctx));
    }
    Err(())
}

fn find_ident<'b>(
    sess: &Session,
    x: &Spanned<Ident>,
    name_context: &NameContext,
    top_level_context: &TopLevelContext,
) -> TypecheckingResult<Ident> {
    match &x.0 {
        Ident::Hacspec(_, _) => {
            sess.span_rustspec_err(
                x.1.clone(),
                "trying to lookup in the name context an already translated id",
            );
            Err(())
        }
        Ident::Original(name) => match name_context.get(name) {
            None => match top_level_context.consts.get(name) {
                Some(_) => Ok(x.0.clone()),
                None => {
                    sess.span_rustspec_err(x.1.clone(), "original id not found in name context");
                    Err(())
                }
            },
            Some(id) => Ok(id.clone()),
        },
    }
}

fn find_typ(
    x: &Ident,
    var_context: &VarContext,
    top_level_context: &TopLevelContext,
) -> Option<Typ> {
    match x {
        Ident::Original(name) => top_level_context
            .consts
            .get(name)
            .map(|(t, _)| ((Borrowing::Consumed, t.1.clone()), t.clone())),
        Ident::Hacspec(id, _) => var_context.get(id).map(|x| x.0.clone()),
    }
}

fn remove_var(x: &Ident, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Original(_) => panic!("trying to lookup in the var context an original id"),
        Ident::Hacspec(id, _) => var_context.without(id),
    }
}

fn add_var(x: &Ident, typ: &Typ, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Original(_) => panic!("trying to lookup in the var context an original id"),
        Ident::Hacspec(id, name) => var_context.update(id.clone(), (typ.clone(), name.clone())),
    }
}

fn add_name(name: &Ident, var: &Ident, name_context: &NameContext) -> NameContext {
    match name {
        Ident::Original(name) => name_context.update(name.clone(), var.clone()),
        Ident::Hacspec(_, _) => panic!("trying to lookup in the name context a Hacspec id"),
    }
}

pub type TypecheckingResult<T> = Result<T, ()>;

fn check_vec<T>(v: Vec<TypecheckingResult<T>>) -> TypecheckingResult<Vec<T>> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn typecheck_expression(
    sess: &Session,
    (e, span): &Spanned<Expression>,
    top_level_context: &TopLevelContext,
    typ_dict: &TypeDict,
    var_context: &VarContext,
    name_context: &NameContext,
) -> TypecheckingResult<(Expression, Typ, VarContext)> {
    match e {
        Expression::Tuple(args) => {
            let mut var_context = var_context.clone();
            let new_and_typ_args = args
                .iter()
                .map(|arg| {
                    let (new_arg, ((arg_typ_borrowing, _), arg_typ), new_var_context) =
                        typecheck_expression(
                            sess,
                            arg,
                            top_level_context,
                            typ_dict,
                            &var_context,
                            name_context,
                        )?;
                    var_context = new_var_context;
                    match arg_typ_borrowing {
                        Borrowing::Borrowed => {
                            sess.span_rustspec_err(
                                arg.1,
                                "borrowed values are forbidden in Hacspec tuples",
                            );
                            Err(())
                        }
                        Borrowing::Consumed => Ok(((new_arg, arg.1.clone()), arg_typ)),
                    }
                })
                .collect();
            let new_and_typ_args = check_vec(new_and_typ_args)?;
            let (new_args, typ_args): (Vec<_>, Vec<_>) = new_and_typ_args.into_iter().unzip();
            Ok((
                Expression::Tuple(new_args),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Tuple(typ_args), span.clone()),
                ),
                var_context,
            ))
        }
        Expression::Named(id) => {
            let id = find_ident(
                sess,
                &(id.clone(), span.clone()),
                name_context,
                top_level_context,
            )?;
            let new_path = Expression::Named(id.clone());
            match find_typ(&id, var_context, top_level_context) {
                None => {
                    sess.span_rustspec_err(
                        *span,
                        format!("the variable {} is not present in the context", id).as_str(),
                    );
                    Err(())
                }
                Some(t) => {
                    // This is where linearity kicks in
                    if let Borrowing::Consumed = (t.0).0 {
                        if is_copy(&(t.1).0, typ_dict) {
                            Ok((new_path, t.clone(), var_context.clone()))
                        } else {
                            let new_var_context = remove_var(&id, var_context);
                            Ok((new_path, t.clone(), new_var_context))
                        }
                    } else {
                        Ok((new_path, t.clone(), var_context.clone()))
                    }
                }
            }
        }
        Expression::Binary((op, op_span), e1, e2, _) => {
            let (new_e1, t1, var_context) = typecheck_expression(
                sess,
                e1,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            let (new_e2, t2, var_context) = typecheck_expression(
                sess,
                e2,
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            match op {
                BinOpKind::Shl | BinOpKind::Shr => match &(t2.1).0 {
                    BaseTyp::UInt32 => {
                        if is_numeric(&t1, typ_dict) {
                            Ok((
                                Expression::Binary(
                                    (op.clone(), op_span.clone()),
                                    Box::new((new_e1, e1.1.clone())),
                                    Box::new((new_e2, e2.1.clone())),
                                    Some(t1.clone()),
                                ),
                                t1,
                                var_context,
                            ))
                        } else {
                            sess.span_rustspec_err(
                                e1.1.clone(),
                                format!(
                                    "you can only shift integers, but found type {}{}",
                                    (t1.0).0,
                                    (t1.1).0
                                )
                                .as_str(),
                            );
                            Err(())
                        }
                    }
                    _ => {
                        sess.span_rustspec_err(
                            e2.1.clone(),
                            format!(
                                "the shifting amount has to be an u32, found type {}{}",
                                (t2.0).0,
                                (t2.1).0
                            )
                            .as_str(),
                        );
                        Err(())
                    }
                },
                _ => {
                    if unify_types(sess, &t1, &t2, &HashMap::new(), typ_dict)?.is_none() {
                        sess.span_rustspec_err(
                            *span,
                            format!(
                                "wrong types of binary operators, left is {}{} while right is {}{}",
                                t1.0.0, t1.1.0, t2.0.0, t2.1.0
                            )
                            .as_str(),
                        );
                        Err(())
                    } else {
                        if is_numeric(&t1, typ_dict)
                            || (match op {
                                BinOpKind::Eq | BinOpKind::Ne => true,
                                _ => false,
                            })
                        {
                            Ok((
                                Expression::Binary(
                                    (op.clone(), op_span.clone()),
                                    Box::new((new_e1, e1.1.clone())),
                                    Box::new((new_e2, e2.1.clone())),
                                    Some(t1.clone()),
                                ),
                                match op {
                                    BinOpKind::Eq
                                    | BinOpKind::Lt
                                    | BinOpKind::Le
                                    | BinOpKind::Ne
                                    | BinOpKind::Ge
                                    | BinOpKind::Gt => {
                                        ((Borrowing::Consumed, (t1.0).1), (BaseTyp::Bool, (t1.1).1))
                                    }
                                    _ => t1,
                                },
                                var_context,
                            ))
                        } else {
                            sess.span_rustspec_err(
                                span.clone(),
                                format!(
                                    "operation not available for type {}{}",
                                    (t1.0).0,
                                    (t1.1).0
                                )
                                .as_str(),
                            );
                            Err(())
                        }
                    }
                }
            }
        }
        Expression::Unary(op, e1, _) => {
            let (new_e1, e1_typ, new_var_context) = typecheck_expression(
                sess,
                e1,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            Ok((
                Expression::Unary(
                    op.clone(),
                    Box::new((new_e1, e1.1.clone())),
                    Some(e1_typ.clone()),
                ),
                e1_typ,
                new_var_context,
            ))
        }
        Expression::Lit(lit) => match lit {
            Literal::Unit => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Unit, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Bool(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Bool, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int128(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int128, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt128(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt128, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int64(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int64, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt64(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt64, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int32(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int32, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt32(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt32, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int16(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int16, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt16(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt16, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int8(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int8, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt8(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt8, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Usize(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Usize, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Isize(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Isize, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Str(_) => Ok((
                e.clone(),
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Str, span.clone()),
                ),
                var_context.clone(),
            )),
        },

        Expression::NewArray(array_type, _, elements) => {
            let (array_len, (cell_type, cell_type_span)) = is_array(
                sess,
                &(
                    (Borrowing::Consumed, array_type.1.clone()),
                    (
                        BaseTyp::Named(array_type.clone(), None),
                        array_type.1.clone(),
                    ),
                ),
                typ_dict,
                &array_type.1,
            )?;
            let array_len = match array_len {
                Some(len) => len,
                None => {
                    sess.span_rustspec_err(
                        array_type.1.clone(),
                        "type should be an array but is Seq",
                    );
                    return Err(());
                }
            };
            match &array_len.0 {
                ArraySize::Integer(array_len) => {
                    if elements.len() != *array_len {
                        sess.span_rustspec_err(
                            span.clone(),
                            format!(
                                "array {} initializer expected {} elements but got {}",
                                array_type.0,
                                array_len,
                                elements.len()
                            )
                            .as_str(),
                        )
                    }
                }
                ArraySize::Ident(_) => (), // we trust Rust typechecking for this case,
                                           // in order to avoid redoing here a const computation engine
            }
            let mut var_context = var_context.clone();
            let new_elements = check_vec(
                elements
                    .iter()
                    .map(|element| {
                        let (new_element, element_typ, new_var_context) = typecheck_expression(
                            sess,
                            element,
                            top_level_context,
                            typ_dict,
                            &var_context,
                            name_context,
                        )?;
                        var_context = new_var_context;
                        match unify_types(
                            sess,
                            &(
                                (Borrowing::Consumed, cell_type_span.clone()),
                                (cell_type.clone(), cell_type_span.clone()),
                            ),
                            &element_typ,
                            &HashMap::new(),
                            typ_dict,
                        )? {
                            None => {
                                sess.span_rustspec_err(
                                    element.1.clone(),
                                    format!(
                                        "expected type {}, got type {}{}",
                                        &cell_type,
                                        &(element_typ.0).0,
                                        &(element_typ.1).0
                                    )
                                    .as_str(),
                                );
                                Err(())
                            }
                            Some(_) => {
                                // Here we can drop the unified variables because there should not be any
                                // unified variables (no generic functions involved)
                                Ok((new_element, element.1.clone()))
                            }
                        }
                    })
                    .collect(),
            )?;
            let new_array_typ = BaseTyp::Array(array_len, Box::new((cell_type, cell_type_span)));
            Ok((
                Expression::NewArray(
                    array_type.clone(),
                    Some(new_array_typ.clone()),
                    new_elements,
                ),
                (
                    (Borrowing::Consumed, array_type.1.clone()),
                    (new_array_typ, array_type.1.clone()),
                ),
                var_context,
            ))
        }
        Expression::ArrayIndex((x, x_span), e2) => {
            let x = find_ident(
                sess,
                &(x.clone(), x_span.clone()),
                name_context,
                top_level_context,
            )?;
            let t1 = match find_typ(&x, var_context, top_level_context) {
                None => {
                    sess.span_rustspec_err(
                        *x_span,
                        format!("the variable {} is unknown", x).as_str(),
                    );
                    return Err(());
                }
                Some(t) => t,
            };
            let (new_e2, t2, var_context) = typecheck_expression(
                sess,
                e2,
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            let (_, (cell_t, cell_t_span)) = is_array(sess, &t1, typ_dict, x_span)?;
            // We ignore t1.0 because we can read from both consumed and borrowed array types
            if let Borrowing::Borrowed = (t2.0).0 {
                sess.span_rustspec_err(e2.1, "cannot index array with a borrowed type");
                return Err(());
            }
            match (t2.1).0 {
                BaseTyp::UInt128
                | BaseTyp::Int128
                | BaseTyp::UInt64
                | BaseTyp::Int64
                | BaseTyp::UInt32
                | BaseTyp::Int32
                | BaseTyp::UInt16
                | BaseTyp::Int16
                | BaseTyp::UInt8
                | BaseTyp::Int8
                | BaseTyp::Usize
                | BaseTyp::Isize => Ok((
                    Expression::ArrayIndex(
                        (x.clone(), x_span.clone()),
                        Box::new((new_e2, e2.1.clone())),
                    ),
                    (
                        (Borrowing::Consumed, (t1.0).1),
                        (cell_t.clone(), cell_t_span.clone()),
                    ),
                    var_context,
                )),

                _ => {
                    sess.span_rustspec_err(
                        e2.1,
                        format!(
                            "expected a public integer to index array but got type {}{}",
                            (t2.0).0,
                            (t2.1).0
                        )
                        .as_str(),
                    );
                    Err(())
                }
            }
        }
        Expression::FuncCall(prefix, name, args) => {
            let (f_sig, typ_var_ctx) = find_func(
                sess,
                &match prefix {
                    None => FnKey::Independent(name.0.clone()),
                    Some((prefix, _)) => FnKey::Impl(prefix.clone(), name.0.clone()),
                },
                top_level_context,
                typ_dict,
                &name.1,
            )?;
            let mut typ_var_ctx = typ_var_ctx;
            if let FnValue::ExternalNotInHacspec(sig_str) = f_sig {
                sess.span_rustspec_err(
                    name.1.clone(),
                    format!(
                        "function {}{} is known but its signature is not in Hacspec: {}",
                        (match prefix {
                            None => String::new(),
                            Some(prefix) => format!("{}::", &prefix.0),
                        }),
                        &name.0,
                        sig_str
                    )
                    .as_str(),
                );
                return Err(());
            };
            let sig_args = sig_args(&f_sig);
            if sig_args.len() != args.len() {
                sess.span_rustspec_err(
                    *span,
                    format!(
                        "function {} was expecting {} arguments but got {}",
                        &name.0,
                        sig_args.len(),
                        args.len()
                    )
                    .as_str(),
                )
            }
            let mut var_context = var_context.clone();
            let mut new_args = Vec::new();
            for (sig_t, ((arg, arg_span), (arg_borrow, arg_borrow_span))) in
                sig_args.iter().zip(args)
            {
                let (new_arg, arg_t, new_var_context) = typecheck_expression(
                    sess,
                    &(arg.clone(), arg_span.clone()),
                    top_level_context,
                    typ_dict,
                    &var_context,
                    name_context,
                )?;
                let new_arg_t = match (&(arg_t.0).0, &arg_borrow) {
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_rustspec_err(
                            *arg_borrow_span,
                            "double borrowing is forbidden in Hacspec!",
                        );
                        return Err(());
                    }
                    (Borrowing::Consumed, Borrowing::Borrowed) => {
                        // If the argument is borrowed, then the consumed variables are actually
                        // not consumed so we don't update the var context
                        ((Borrowing::Borrowed, (arg_t.0).1.clone()), arg_t.1.clone())
                    }
                    _ => {
                        var_context = new_var_context;
                        arg_t.clone()
                    }
                };
                new_args.push((
                    (new_arg, arg_span.clone()),
                    (arg_borrow.clone(), arg_borrow_span.clone()),
                ));
                match unify_types(sess, &new_arg_t, sig_t, &typ_var_ctx, typ_dict)? {
                    None => {
                        sess.span_rustspec_err(
                            *arg_span,
                            format!(
                                "expected type {}{} for function argument, got {}{}",
                                (sig_t.0).0,
                                (sig_t.1).0,
                                (arg_t.0).0,
                                (arg_t.1).0
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                    Some(new_ctx) => typ_var_ctx = new_ctx,
                }
            }
            let ret_ty = sig_ret(&f_sig);
            let ret_ty = bind_variable_type(sess, &(ret_ty.clone(), span.clone()), &typ_var_ctx)?;
            Ok((
                Expression::FuncCall(prefix.clone(), name.clone(), new_args),
                (
                    (Borrowing::Consumed, name.1.clone()),
                    (ret_ty, name.1.clone()),
                ),
                var_context,
            ))
        }
        Expression::MethodCall(sel, _, (f, f_span), orig_args) => {
            let (sel, sel_borrow) = sel.as_ref();
            let mut var_context = var_context.clone();
            // We omit to take the new var context because it will be retypechecked later, this
            // is just to determine wich type the method belongs to
            let (_, sel_typ, _) = typecheck_expression(
                sess,
                &sel,
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            let (f_sig, typ_var_ctx) = find_func(
                sess,
                &FnKey::Impl((sel_typ.1).0.clone(), f.clone()),
                top_level_context,
                typ_dict,
                f_span,
            )?;
            let mut typ_var_ctx = typ_var_ctx;
            if let FnValue::ExternalNotInHacspec(_) = f_sig {
                sess.span_rustspec_err(
                    *f_span,
                    format!(
                        "function {}::{} is known but its signature is not in Hacspec",
                        (sel_typ.1).0,
                        f
                    )
                    .as_str(),
                );
                return Err(());
            };
            let sig_args = sig_args(&f_sig);
            // Because self arguments are implictly borrowed in Rust, we have to insert
            // this implicit borrow logic here
            let new_sel_borrow = match (
                &sel_borrow.0,
                &(sel_typ.0).0,
                &(sig_args.first().unwrap().0).0,
            ) {
                (Borrowing::Consumed, Borrowing::Consumed, Borrowing::Borrowed) => {
                    (Borrowing::Borrowed, sel_borrow.1.clone())
                }
                _ => sel_borrow.clone(),
            };
            let mut args = Vec::new();
            args.push((sel.clone(), new_sel_borrow.clone()));
            args.extend(orig_args.clone());
            let mut new_args = Vec::new();
            if sig_args.len() != args.len() {
                sess.span_rustspec_err(
                    *span,
                    format!(
                        "method {}::{} was expecting {} arguments but got {}",
                        (sel_typ.1).0,
                        f,
                        sig_args.len(),
                        args.len()
                    )
                    .as_str(),
                )
            }
            for (sig_t, ((arg, arg_span), (arg_borrow, arg_borrow_span))) in
                sig_args.iter().zip(args)
            {
                let (new_arg, arg_t, new_var_context) = typecheck_expression(
                    sess,
                    &(arg.clone(), arg_span.clone()),
                    top_level_context,
                    typ_dict,
                    &var_context,
                    name_context,
                )?;

                let new_arg_t = match (&(arg_t.0).0, &arg_borrow) {
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_rustspec_err(
                            arg_borrow_span,
                            "double borrowing is forbidden in Hacspec!",
                        );
                        return Err(());
                    }
                    (Borrowing::Consumed, Borrowing::Borrowed) => {
                        // If the argument is borrowed, then the consumed variables are actually
                        // not consumed so we don't update the var context
                        ((Borrowing::Borrowed, (arg_t.0).1.clone()), arg_t.1.clone())
                    }
                    _ => {
                        var_context = new_var_context;
                        arg_t.clone()
                    }
                };
                new_args.push((
                    (new_arg, arg_span.clone()),
                    (arg_borrow.clone(), arg_borrow_span.clone()),
                ));
                match unify_types(sess, &new_arg_t, sig_t, &typ_var_ctx, typ_dict)? {
                    None => {
                        sess.span_rustspec_err(
                            arg_span,
                            format!(
                                "expected type {}{}, got {}{}",
                                (sig_t.0).0,
                                (sig_t.1).0,
                                (new_arg_t.0).0,
                                (new_arg_t.1).0
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                    Some(new_ctx) => typ_var_ctx = new_ctx,
                }
            }
            let new_sel = new_args.first().unwrap().clone();
            new_args = new_args[1..].to_vec();
            let ret_ty = sig_ret(&f_sig);
            let ret_ty = bind_variable_type(sess, &(ret_ty.clone(), span.clone()), &typ_var_ctx)?;
            Ok((
                Expression::MethodCall(
                    Box::new(new_sel),
                    Some(sel_typ),
                    (f.clone(), f_span.clone()),
                    new_args,
                ),
                (
                    (Borrowing::Consumed, f_span.clone()),
                    (ret_ty, f_span.clone()),
                ),
                var_context,
            ))
        }
        Expression::IntegerCasting(e1, t1) => {
            let (new_e1, e1_typ, var_context) = typecheck_expression(
                sess,
                e1,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            if (e1_typ.0).0 == Borrowing::Borrowed {
                sess.span_rustspec_err(e1.1.clone(), "cannot cast borrowed expression");
                return Err(());
            }
            if !is_castable_integer(&(e1_typ.1).0) {
                sess.span_rustspec_err(e1.1.clone(), "this expression cannot be casted");
                return Err(());
            }
            if !is_castable_integer(&t1.0) {
                sess.span_rustspec_err(e1.1.clone(), "impossible to cast to this type");
                return Err(());
            }
            if !is_safe_casting(&(e1_typ.1).0, &t1.0) {
                sess.span_rustspec_err(
                    span.clone(),
                    format!("casting from {} to {} is not safe (i.e it can lead to overflow)",
                        &e1_typ.1.0,
                        &t1.0
                    )
                    .as_str(),
                );
                return Err(());
            }
            Ok((
                Expression::IntegerCasting(Box::new((new_e1, e1.1.clone())), t1.clone()),
                ((Borrowing::Consumed, t1.1.clone()), t1.clone()),
                var_context,
            ))
        }
    }
}

fn typecheck_pattern(
    sess: &Session,
    (pat, pat_span): &Spanned<Pattern>,
    (borrowing_typ, typ): &Typ,
) -> TypecheckingResult<(Pattern, VarContext, NameContext)> {
    match (pat, &typ.0) {
        (Pattern::Tuple(pat_args), BaseTyp::Tuple(ref typ_args)) => {
            if pat_args.len() != typ_args.len() {
                sess.span_rustspec_err(*pat_span,
                    format!("let-binding tuple pattern has {} variables but {} were expected from the type",
                     pat_args.len(),
                     typ_args.len()).as_str()
                )
            };
            let (tup_args, acc_var, acc_name) = pat_args.iter().zip(typ_args.iter()).fold(
                Ok((Vec::new(), HashMap::new(), HashMap::new())),
                |acc, (pat_arg, typ_arg)| {
                    let (mut acc_pat, acc_var, acc_name) = acc?;
                    let (new_pat, sub_var_context, sub_name_context) = typecheck_pattern(
                        sess,
                        pat_arg,
                        //TODO: changed to propagate borrow to tuple args
                        &((Borrowing::Consumed, *pat_span), typ_arg.clone()),
                    )?;
                    acc_pat.push((new_pat, pat_arg.1.clone()));
                    Ok((
                        acc_pat,
                        acc_var.union(sub_var_context),
                        acc_name.union(sub_name_context),
                    ))
                },
            )?;
            Ok((Pattern::Tuple(tup_args), acc_var, acc_name))
        }
        (Pattern::Tuple(_), _) => {
            sess.span_rustspec_err(
                *pat_span,
                format!(
                    "let-binding pattern expected a tuple but the type is {}",
                    typ.0
                )
                .as_str(),
            );
            Err(())
        }
        (Pattern::WildCard, _) => Ok((Pattern::WildCard, HashMap::new(), HashMap::new())),
        (Pattern::IdentPat(x), _) => {
            let x_new = fresh_ident(x);
            let (id, name) = match &x_new {
                Ident::Hacspec(id, name) => (id.clone(), name.clone()),
                _ => panic!(), // shouls not happen
            };
            Ok((
                Pattern::IdentPat(x_new.clone()),
                HashMap::unit(id, ((borrowing_typ.clone(), typ.clone()), name)),
                HashMap::unit(
                    match &x {
                        Ident::Original(name) => name.clone(),
                        _ => panic!(), // should not happen
                    },
                    x_new.clone(),
                ),
            ))
        }
    }
}

fn var_set_to_tuple(vars: &VarSet, span: &Span) -> Statement {
    Statement::ReturnExp(if vars.len() > 0 {
        Expression::Tuple(
            vars.iter()
                .map(|i| (Expression::Named(i.clone()), span.clone()))
                .collect(),
        )
    } else {
        Expression::Lit(Literal::Unit)
    })
}

fn typecheck_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    top_level_context: &TopLevelContext,
    typ_dict: &TypeDict,
    var_context: &VarContext,
    name_context: &NameContext,
) -> TypecheckingResult<(Statement, Typ, VarContext, NameContext, VarSet)> {
    match &s {
        Statement::LetBinding((pat, pat_span), typ, ref expr) => {
            let (new_expr, expr_typ, new_var_context) = typecheck_expression(
                sess,
                expr,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            match typ {
                None => (),
                Some((typ, _)) => {
                    if unify_types(sess, typ, &expr_typ, &HashMap::new(), typ_dict)?.is_none() {
                        sess.span_rustspec_err(
                            *pat_span,
                            format!(
                                "wrong type declared for variable: expected {}{}, found {}{}",
                                (typ.0).0,
                                (typ.1).0,
                                (expr_typ.0).0,
                                (expr_typ.1).0
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                }
            };
            let (new_pat, pat_var_context, pat_name_context) =
                typecheck_pattern(sess, &(pat.clone(), pat_span.clone()), &expr_typ)?;
            Ok((
                Statement::LetBinding(
                    (new_pat, pat_span.clone()),
                    typ.clone(),
                    (new_expr, expr.1.clone()),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                new_var_context.clone().union(pat_var_context),
                pat_name_context.union(name_context.clone()),
                HashSet::new(),
            ))
        }
        Statement::Reassignment((x, x_span), e) => {
            let x = find_ident(
                sess,
                &(x.clone(), x_span.clone()),
                name_context,
                top_level_context,
            )?;
            let (new_e, e_typ, new_var_context) = typecheck_expression(
                sess,
                &e,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            let x_typ = find_typ(&x, var_context, top_level_context);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_rustspec_err(*x_span, "trying to reassign to an inexisting variable");
                    return Err(());
                }
            };
            if unify_types(sess, &e_typ, &x_typ, &HashMap::new(), typ_dict)?.is_none() {
                sess.span_rustspec_err(
                    e.1,
                    format!(
                        "variable {} has type {}{} but tried to reassign with an expression of type {}{}",
                        x, (x_typ.0).0, (x_typ.1).0, (e_typ.0).0, (e_typ.1).0
                    ).as_str(),
                );
                return Err(());
            };
            Ok((
                Statement::Reassignment((x.clone(), x_span.clone()), (new_e, e.1.clone())),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                add_var(&x, &x_typ, &new_var_context),
                name_context.clone(),
                HashSet::unit(x.clone()),
            ))
        }
        Statement::ArrayUpdate((x, x_span), e1, e2) => {
            let x = find_ident(
                sess,
                &(x.clone(), x_span.clone()),
                name_context,
                top_level_context,
            )?;
            let (new_e1, e1_t, var_context) = typecheck_expression(
                sess,
                &e1,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            let (new_e2, e2_t, var_context) = typecheck_expression(
                sess,
                &e2,
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            if !is_index(&(e1_t.1).0) {
                sess.span_rustspec_err(
                    e1.1,
                    format!(
                        "index should have an integer type but instead has {}{}",
                        (e1_t.0).0,
                        (e1_t.1).0,
                    )
                    .as_str(),
                );
                return Err(());
            };
            let x_typ = find_typ(&x, &var_context, top_level_context);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_rustspec_err(*x_span, "trying to update an inexisting array");
                    return Err(());
                }
            };
            let (_, cell_t) = is_array(sess, &x_typ, typ_dict, x_span)?;
            if unify_types(
                sess,
                &e2_t,
                &((Borrowing::Consumed, x_span.clone()), cell_t.clone()),
                &HashMap::new(),
                typ_dict,
            )?
            .is_none()
            {
                sess.span_rustspec_err(
                    e2.1,
                    format!(
                        "array {} has cells of type {} but tried to reassign cell with an expression of type {}{}",
                        x, cell_t.0, (e2_t.0).0, (e2_t.1).0
                    ).as_str(),
                );
                return Err(());
            };
            Ok((
                Statement::ArrayUpdate(
                    (x.clone(), x_span.clone()),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                var_context,
                name_context.clone(),
                HashSet::unit(x.clone()),
            ))
        }
        Statement::ReturnExp(e) => {
            let (new_e, e_t, var_context) = typecheck_expression(
                sess,
                &(e.clone(), s_span),
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            Ok((
                Statement::ReturnExp(new_e),
                e_t,
                var_context,
                name_context.clone(),
                HashSet::new(),
            ))
        }
        Statement::Conditional(cond, (b1, b1_span), b2, _) => {
            let original_var_context = var_context;
            let (new_cond, cond_t, var_context) = typecheck_expression(
                sess,
                &cond,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            match cond_t {
                ((Borrowing::Consumed, _), (BaseTyp::Bool, _)) => (),
                _ => sess.span_rustspec_err(
                    cond.1,
                    format!(
                        "if condition should have type bool but has type {}{}",
                        (cond_t.0).0,
                        (cond_t.1).0
                    )
                    .as_str(),
                ),
            }
            let (new_b1, var_context_b1) = typecheck_block(
                sess,
                (b1.clone(), b1_span.clone()),
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            let (new_b2, var_context_b2) = match b2 {
                None => (None, var_context.clone()),
                Some((b2, b2_span)) => {
                    let (new_b2, var_context_b2) = typecheck_block(
                        sess,
                        (b2.clone(), b2_span.clone()),
                        top_level_context,
                        typ_dict,
                        &var_context,
                        name_context,
                    )?;
                    (Some((new_b2, *b2_span)), var_context_b2)
                }
            };
            match &new_b1.return_typ {
                None => panic!(), // should not happen
                Some(((Borrowing::Consumed, _), (BaseTyp::Unit, _))) => (),
                Some(((b_t, _), (t, _))) => {
                    sess.span_rustspec_err(
                        *b1_span,
                        format!("block has return type {}{} but was expecting unit", b_t, t)
                            .as_str(),
                    );
                    return Err(());
                }
            };
            match &new_b2 {
                None => (),
                Some((new_b2, _)) => {
                    match &new_b2.return_typ {
                        None => panic!(), // should not happen
                        Some(((Borrowing::Consumed, _), (BaseTyp::Unit, _))) => (),
                        Some(((b_t, _), (t, _))) => {
                            sess.span_rustspec_err(
                                *b1_span,
                                format!(
                                    "block has return type {}{} but was expecting unit",
                                    b_t, t
                                )
                                .as_str(),
                            );
                            return Err(());
                        }
                    };
                }
            }
            let new_mutated = match &new_b1.mutated {
                None => HashSet::new(),
                Some(m) => m.vars.clone(),
            }
            .union(match &new_b2 {
                None => HashSet::new(),
                Some((new_b2, _)) => match &new_b2.mutated {
                    None => HashSet::new(),
                    Some(m) => m.vars.clone(),
                },
            });
            let mut_tuple = var_set_to_tuple(&new_mutated, &s_span);
            Ok((
                Statement::Conditional(
                    (new_cond, cond.1.clone()),
                    (new_b1, *b1_span),
                    new_b2,
                    Some(Box::new(MutatedInfo {
                        vars: new_mutated.clone(),
                        stmt: mut_tuple,
                    })),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                original_var_context
                    .clone()
                    .intersection(var_context_b1)
                    .intersection(var_context_b2),
                name_context.clone(),
                new_mutated,
            ))
        }
        Statement::ForLoop((old_x, x_span), e1, e2, (b, b_span)) => {
            let x = fresh_ident(old_x);
            let original_var_context = var_context;
            let (new_e1, t_e1, var_context) = typecheck_expression(
                sess,
                e1,
                top_level_context,
                typ_dict,
                var_context,
                name_context,
            )?;
            let (new_e2, t_e2, var_context) = typecheck_expression(
                sess,
                e2,
                top_level_context,
                typ_dict,
                &var_context,
                name_context,
            )?;
            match &t_e1 {
                ((Borrowing::Consumed, _), (BaseTyp::Usize, _)) => (),
                _ => {
                    sess.span_rustspec_err(
                        e1.1,
                        format!(
                            "loop range bound should be an integer but has type {}{}",
                            (t_e1.0).0,
                            (t_e1.1).0
                        )
                        .as_str(),
                    );
                    return Err(());
                }
            };
            match &t_e2 {
                ((Borrowing::Consumed, _), (BaseTyp::Usize, _)) => (),
                _ => {
                    sess.span_rustspec_err(
                        e2.1,
                        format!(
                            "loop range bound should be an integer but has type {}{}",
                            (t_e2.0).0,
                            (t_e2.1).0
                        )
                        .as_str(),
                    );
                    return Err(());
                }
            };
            let var_context = add_var(
                &x,
                &((Borrowing::Consumed, *x_span), (BaseTyp::Usize, *x_span)),
                &var_context,
            );
            let new_name_context = name_context.update(
                match old_x {
                    Ident::Original(name) => name.clone(),
                    _ => panic!(), // should not happen
                },
                x.clone(),
            );
            let (new_b, var_context) = typecheck_block(
                sess,
                (b.clone(), b_span.clone()),
                top_level_context,
                typ_dict,
                &var_context,
                &new_name_context,
            )?;
            let mutated_vars = new_b.mutated.as_ref().unwrap().as_ref().vars.clone();
            // Linear variables cannot be consumed in the body of the loop, so we check that
            let var_diff = original_var_context.clone().difference(var_context.clone());
            for (var_diff_id, (_, var_diff_name)) in var_diff {
                if original_var_context.contains_key(&var_diff_id) {
                    sess.span_rustspec_err(
                        b_span.clone(),
                        format!("loop body consumes linear variable: {}", var_diff_name).as_str(),
                    );
                    return Err(());
                }
            }
            Ok((
                Statement::ForLoop(
                    (x.clone(), *x_span),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                    (new_b, *b_span),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                original_var_context.clone().intersection(var_context),
                name_context.clone(),
                mutated_vars,
            ))
        }
    }
}

fn typecheck_block(
    sess: &Session,
    (b, b_span): Spanned<Block>,
    top_level_context: &TopLevelContext,
    typ_dict: &TypeDict,
    original_var_context: &VarContext,
    name_context: &NameContext,
) -> TypecheckingResult<(Block, VarContext)> {
    let mut var_context = original_var_context.clone();
    let mut name_context = name_context.clone();
    let mut mutated_vars = HashSet::new();
    let mut return_typ = None;
    let mut new_stmts = Vec::new();
    let n_stmts = b.stmts.len();
    for (i, s) in b.stmts.into_iter().enumerate() {
        let s_span = s.1.clone();
        let (new_stmt, stmt_typ, new_var_context, new_name_context, new_mutated_vars) =
            typecheck_statement(
                sess,
                s,
                top_level_context,
                typ_dict,
                &var_context,
                &name_context,
            )?;
        new_stmts.push((new_stmt, s_span));
        var_context = new_var_context;
        name_context = new_name_context;
        mutated_vars = mutated_vars.clone().union(new_mutated_vars);
        if i + 1 < n_stmts {
            // Statement return types should be unit except for the last one
            match stmt_typ {
                ((Borrowing::Consumed, _), (BaseTyp::Unit, _)) => (),
                _ => {
                    sess.span_rustspec_err(s_span, "statement shoud have an unit type here");
                    return Err(());
                }
            }
        } else {
            return_typ = Some(stmt_typ)
        }
    }
    let mut_tuple = var_set_to_tuple(&mutated_vars, &b_span);
    Ok((
        Block {
            stmts: new_stmts,
            mutated: Some(Box::new(MutatedInfo {
                vars: mutated_vars,
                stmt: mut_tuple,
            })),
            return_typ,
        },
        var_context.intersection(original_var_context.clone()),
    ))
}

fn typecheck_item(
    sess: &Session,
    i: &Item,
    top_level_context: &TopLevelContext,
    typ_dict: &TypeDict,
) -> TypecheckingResult<(Item, TopLevelContext, TypeDict)> {
    match &i {
        Item::FnDecl((f, f_span), sig, (b, b_span)) => {
            let var_context = HashMap::new();
            let name_context = HashMap::new();
            let (new_sig_args, var_context, name_context) = sig.args.iter().fold(
                (Vec::new(), var_context, name_context),
                |(mut new_sig_acc, var_context, name_context), ((x, x_span), (t, t_span))| {
                    let new_x = fresh_ident(x);
                    let name_context = add_name(x, &new_x, &name_context);
                    let var_context = add_var(&new_x, t, &var_context);
                    new_sig_acc.push(((new_x, x_span.clone()), (t.clone(), t_span.clone())));
                    (new_sig_acc, var_context, name_context)
                },
            );
            let out = Item::FnDecl(
                (f.clone(), f_span.clone()),
                FuncSig {
                    args: new_sig_args,
                    ret: sig.ret.clone(),
                },
                (
                    typecheck_block(
                        sess,
                        (b.clone(), b_span.clone()),
                        top_level_context,
                        typ_dict,
                        &var_context,
                        &name_context,
                    )?
                    .0,
                    b_span.clone(),
                ),
            );
            let new_functions = top_level_context
                .functions
                .update(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
            let mut top_level_context = top_level_context.clone();
            top_level_context.functions = new_functions;
            Ok((out, top_level_context, typ_dict.clone()))
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let (new_size, size_typ, _) = typecheck_expression(
                sess,
                size,
                top_level_context,
                typ_dict,
                &HashMap::new(),
                &HashMap::new(),
            )?;
            if let None = unify_types(
                sess,
                &(
                    (Borrowing::Consumed, size.1.clone()),
                    (BaseTyp::Usize, size.1.clone()),
                ),
                &size_typ,
                &HashMap::new(),
                typ_dict,
            )? {
                sess.span_rustspec_err(
                    size.1.clone(),
                    format!(
                        "expected type usize, got {}{}",
                        (size_typ.0).0,
                        (size_typ.1).0
                    )
                    .as_str(),
                )
            }
            let new_size = match new_size {
                Expression::Lit(Literal::Usize(u)) => ArraySize::Integer(u),
                Expression::Named(Ident::Original(s)) => ArraySize::Ident(s),
                _ => {
                    sess.span_rustspec_err(
                        size.1.clone(),
                        "expected identifier or integer literal",
                    );
                    return Err(());
                }
            };
            let typ_dict = match index_typ {
                None => typ_dict.clone(),
                Some(index_typ) => typ_dict.update(
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
                ),
            };
            Ok((
                i.clone(),
                top_level_context.clone(),
                typ_dict.update(
                    match &id.0 {
                        Ident::Original(s) => s.clone(),
                        Ident::Hacspec(_, _) => panic!(),
                    },
                    (
                        (
                            (Borrowing::Consumed, id.1.clone()),
                            (
                                BaseTyp::Array(
                                    (new_size, size.1.clone()),
                                    Box::new(cell_t.clone()),
                                ),
                                id.1.clone(),
                            ),
                        ),
                        DictEntry::Array,
                    ),
                ),
            ))
        }
        Item::ConstDecl(id, typ, e) => {
            let (new_e, new_t, _) = typecheck_expression(
                sess,
                e,
                top_level_context,
                typ_dict,
                &HashMap::new(),
                &HashMap::new(),
            )?;
            if let None = unify_types(
                sess,
                &((Borrowing::Consumed, typ.1.clone()), typ.clone()),
                &new_t,
                &HashMap::new(),
                typ_dict,
            )? {
                sess.span_rustspec_err(
                    e.1.clone(),
                    format!(
                        "expected type {}, got type {}{}",
                        typ.0,
                        (new_t.0).0,
                        (new_t.1).0
                    )
                    .as_str(),
                );
                return Err(());
            }
            let mut top_level_context = top_level_context.clone();
            top_level_context.consts = top_level_context.consts.update(
                match id {
                    (Ident::Original(id), _) => id.clone(),
                    _ => panic!(), // should not happen
                },
                (typ.clone(), (new_e.clone(), e.1.clone())),
            );
            Ok((
                Item::ConstDecl(id.clone(), typ.clone(), (new_e, (e.1).clone())),
                top_level_context,
                typ_dict.clone(),
            ))
        }
        Item::NaturalIntegerDecl(typ_ident, canvas_typ_ident, secrecy, canvas_size, mod_string) => {
            let (_, top_level_context, typ_dict) = typecheck_item(
                sess,
                &Item::ArrayDecl(
                    canvas_typ_ident.clone(),
                    canvas_size.clone(),
                    match secrecy {
                        Secrecy::Secret => (
                            BaseTyp::Named(
                                (
                                    Ident::Original("U8".to_string()),
                                    canvas_typ_ident.1.clone(),
                                ),
                                None,
                            ),
                            canvas_typ_ident.1.clone(),
                        ),
                        Secrecy::Public => (BaseTyp::UInt8, canvas_typ_ident.1.clone()),
                    },
                    None,
                ),
                top_level_context,
                typ_dict,
            )?;
            let typ_dict = typ_dict.update(
                match &typ_ident.0 {
                    Ident::Original(s) => s.clone(),
                    Ident::Hacspec(_, _) => panic!(),
                },
                (
                    (
                        (Borrowing::Consumed, typ_ident.1.clone()),
                        (
                            BaseTyp::NaturalInteger(secrecy.clone(), mod_string.clone()),
                            typ_ident.1.clone(),
                        ),
                    ),
                    DictEntry::NaturalInteger,
                ),
            );
            Ok((i.clone(), top_level_context, typ_dict))
        }
    }
}

pub fn typecheck_program<
    F: Fn(
        &Vec<Spanned<String>>,
    ) -> (
        HashMap<FnKey, Result<ExternalFuncSig, String>>,
        HashMap<String, BaseTyp>,
    ),
>(
    sess: &Session,
    p: &Program,
    external_funcs: &F,
    _allowed_sigs: &AllowedSigs,
) -> TypecheckingResult<(Program, TypeDict)> {
    let (extern_funcs, extern_arrays) = external_funcs(&p.imported_crates);
    let mut top_level_context: TopLevelContext = TopLevelContext {
        functions: extern_funcs
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    match v {
                        Ok(v) => FnValue::External(v.clone()),
                        Err(s) => FnValue::ExternalNotInHacspec(s.clone()),
                    },
                )
            })
            .collect(),
        consts: HashMap::new(),
    };
    //TODO: better system, this whitelist is hardcoded
    let mut typ_dict = HashMap::from(
        vec![
            // Handle type aliases in a more systematic way, this is another harcoded list
            (
                String::from("ByteSeq"),
                (
                    (
                        (Borrowing::Consumed, DUMMY_SP),
                        (
                            BaseTyp::Seq(Box::new((
                                BaseTyp::Named((Ident::Original("U8".to_string()), DUMMY_SP), None),
                                DUMMY_SP,
                            ))),
                            DUMMY_SP,
                        ),
                    ),
                    DictEntry::Alias,
                ),
            ),
        ]
        .as_slice(),
    );
    for (array_name, array_typ) in extern_arrays {
        typ_dict.insert(
            array_name,
            (
                ((Borrowing::Consumed, DUMMY_SP), (array_typ, DUMMY_SP)),
                DictEntry::Array,
            ),
        );
    }
    Ok((
        Program {
            items: check_vec(
                p.items
                    .iter()
                    .map(|(i, i_span)| {
                        let (new_i, new_top_level_context, new_typ_dict) =
                            typecheck_item(sess, i, &top_level_context, &typ_dict)?;
                        top_level_context = new_top_level_context;
                        typ_dict = new_typ_dict;
                        Ok((new_i, i_span.clone()))
                    })
                    .collect(),
            )?,
            imported_crates: p.imported_crates.clone(),
        },
        typ_dict,
    ))
}
