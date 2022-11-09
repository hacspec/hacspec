use crate::name_resolution::{DictEntry, FnKey, FnValue, TopLevelContext};
use crate::rustspec::*;
use crate::util::check_vec;
use crate::HacspecErrorEmitter;
use std::convert::{Into, TryInto};

use im::{HashMap, HashSet};
use itertools::Itertools;
use rustc_session::Session;
use rustc_span::DUMMY_SP;

// TODO: explain that we need typechecking inference to disambiguate method calls

fn is_numeric(t: &Typ, top_ctxt: &TopLevelContext) -> bool {
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
        BaseTyp::Named((name, _), None) => match top_ctxt.typ_dict.get(name) {
            Some((new_t1, dict_entry)) => {
                assert!((new_t1.0).0 == Borrowing::Consumed);
                match dict_entry {
                    DictEntry::Alias => is_numeric(new_t1, top_ctxt),
                    DictEntry::Enum => false,
                    DictEntry::Array | DictEntry::NaturalInteger => true,
                }
            }
            None => match name.string.as_str() {
                "U8" | "U16" | "U32" | "U64" | "U128" | "I8" | "I16" | "I32" | "I64" | "I128" => {
                    true
                }
                _ => false,
            },
        },
        BaseTyp::Array(_, _) => true,
        BaseTyp::Seq(t1) => is_numeric(
            &((Borrowing::Consumed, DUMMY_SP.into()), *t1.clone()),
            top_ctxt,
        ),
        _ => false,
    }
}

fn is_bool(t: &Typ, top_ctxt: &TopLevelContext) -> bool {
    if (t.0).0 == Borrowing::Borrowed {
        return false;
    };
    match &(t.1).0 {
        BaseTyp::Bool => true,
        BaseTyp::Named((name, _), None) => match top_ctxt.typ_dict.get(name) {
            Some((new_t1, dict_entry)) => {
                assert!((new_t1.0).0 == Borrowing::Consumed);
                match dict_entry {
                    DictEntry::Alias => is_numeric(new_t1, top_ctxt),
                    DictEntry::Enum | DictEntry::Array | DictEntry::NaturalInteger => false,
                }
            }
            None => false,
        },
        _ => false,
    }
}

fn is_copy(t: &BaseTyp, top_ctxt: &TopLevelContext) -> bool {
    match t {
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
        BaseTyp::Named((name, _), arg) => match top_ctxt.typ_dict.get(name) {
            Some((new_t1, _dict_entry)) => {
                debug_assert!((new_t1.0).0 == Borrowing::Consumed);
                is_copy(&(new_t1.1).0, top_ctxt)
            }
            None => match arg {
                None => match name.string.as_str() {
                    "U8" | "U16" | "U32" | "U64" | "U128" | "I8" | "I16" | "I32" | "I64"
                    | "I128" => true,
                    _ => false,
                },
                Some(_) => false,
            },
        },
        BaseTyp::Variable(_) => false,
        BaseTyp::Tuple(ts) => ts.iter().all(|(t, _)| is_copy(t, top_ctxt)),
        BaseTyp::Enum(ts, type_args) => {
            type_args.len() == 0
                && ts.iter().all(|(_, t)| match t {
                    None => true,
                    Some((t, _)) => is_copy(t, top_ctxt),
                })
        }
        BaseTyp::NaturalInteger(_, _, _) => true,
    }
}

fn is_array(
    sess: &Session,
    t: &Typ,
    top_ctxt: &TopLevelContext,
    span: &RustspecSpan,
) -> Result<(Option<Spanned<ArraySize>>, Spanned<BaseTyp>), ()> {
    match &(t.1).0 {
        BaseTyp::Seq(t1) => Ok((None, t1.as_ref().clone())),
        BaseTyp::Named(id, None) => {
            let name = &id.0;
            match top_ctxt.typ_dict.get(name) {
                Some((new_t, dict_entry)) => match dict_entry {
                    DictEntry::Alias => is_array(sess, new_t, top_ctxt, span),
                    DictEntry::Enum => {
                        sess.span_rustspec_err(
                            span.clone(),
                            format!("expected an array but got type {}{}", &(t.0).0, &(t.1).0)
                                .as_str(),
                        );
                        Err(())
                    }
                    DictEntry::Array => match &(new_t.1).0 {
                        BaseTyp::Array(size, cell_t) => {
                            Ok((Some(size.clone()), cell_t.as_ref().clone()))
                        }
                        _ => panic!("should not happen"),
                    },
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
            }
        }
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

fn is_index(t: &BaseTyp, top_ctxt: &TopLevelContext) -> bool {
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
        BaseTyp::Named((name, _), None) => match top_ctxt.typ_dict.get(name) {
            Some((((Borrowing::Consumed, _), (new_ty, _)), DictEntry::Alias)) => {
                is_index(new_ty, top_ctxt)
            }
            _ => false,
        },
        _ => false,
    }
}

fn is_castable_integer(t: &BaseTyp, top_ctxt: &TopLevelContext) -> bool {
    let t = dealias_type(t.clone(), top_ctxt);
    log::trace!("is_castable_integer {}", t);
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
        (BaseTyp::UInt16, BaseTyp::UInt8) => true,
        (BaseTyp::Usize, BaseTyp::UInt16) | (BaseTyp::Usize, BaseTyp::UInt8) => true,
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
        (BaseTyp::Int16, BaseTyp::Int8) => true,
        (BaseTyp::Isize, BaseTyp::UInt16) | (BaseTyp::Isize, BaseTyp::UInt8) => true,
        _ => false,
    }
}

type TypeVarCtx = HashMap<TypVar, BaseTyp>;

// This function returns Err(_) if there are borrowing problems during unification,
// Ok(None) if unification failed because of incompatible types, and
// Ok(Some(_)) if unification succeeded
fn unify_types(
    sess: &Session,
    t1: &Typ,
    t2: &Typ,
    typ_ctx: &TypeVarCtx,
    top_ctx: &TopLevelContext,
) -> TypecheckingResult<Option<TypeVarCtx>> {
    // We first have to remove all the aliases
    // We don't support generic aliases for now
    match &(t1.1).0 {
        BaseTyp::Named((name1, _), None) => match top_ctx.typ_dict.get(name1) {
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
                    top_ctx,
                );
            }
            _ => (),
        },
        _ => (),
    }
    //Same thing for t2
    match &(t2.1).0 {
        BaseTyp::Named((name2, _), None) => match top_ctx.typ_dict.get(name2) {
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
                    top_ctx,
                );
            }
            _ => (),
        },
        _ => (),
    }

    match (&(t1.0).0, &(t2.0).0) {
        (Borrowing::Consumed, Borrowing::Consumed) | (Borrowing::Borrowed, Borrowing::Borrowed) => {
            match (&(t1.1).0, &(t2.1).0) {
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
                    top_ctx,
                ),
                (BaseTyp::Named(name1, args1), BaseTyp::Named(name2, args2)) => {
                    let (name1, name2) = match (&name1.0, &name2.0) {
                        (
                            TopLevelIdent { string: name1, .. },
                            TopLevelIdent { string: name2, .. },
                        ) => (name1.clone(), name2.clone()),
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
                                                top_ctx,
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
                                        top_ctx,
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
        // We don't need to unify the enum types since they're already dealt
        // with by the Named case (nominal typing)
        _ => Ok(None),
    }
}

fn unify_types_default_error_message(
    sess: &Session,
    t1: &Typ,
    t2: &Typ,
    typ_ctx: &TypeVarCtx,
    top_ctx: &TopLevelContext,
) -> TypecheckingResult<TypeVarCtx> {
    match unify_types(sess, t1, t2, typ_ctx, top_ctx) {
        Err(err) => Err(err),
        Ok(Some(x)) => Ok(x),
        Ok(None) => {
            sess.span_rustspec_err(
                (t1.1).1.clone(),
                format!(
                    "error while unifying {}{} and {}{}",
                    (t1.0).0,
                    (t1.1).0,
                    (t2.0).0,
                    (t2.1).0
                )
                .as_str(),
            );
            Err(())
        }
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
                    format!("type {} cannot be unified, Hacspec does not handle that kind of parametricity", ty.0).as_str(),
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

#[derive(Clone)]
struct VarContext {
    vars: HashMap<usize, (Typ, String, bool)>, // Type, Name, mutable
    mutable_vars: HashMap<usize, (Typ, String, bool)>, // Type, Name, External
}

impl VarContext {
    fn new() -> Self {
        Self {
            vars: HashMap::new(),
            mutable_vars: HashMap::new(),
        }
    }

    fn unit(key: usize, value: (Typ, String, bool), external: bool) -> Self {
        Self {
            vars: HashMap::unit(key, value.clone()),
            mutable_vars: if value.2 {
                HashMap::unit(key, (value.0, value.1, external))
            } else {
                HashMap::new()
            },
        }
    }

    fn union(self, other: Self) -> Self {
        Self {
            vars: self.vars.union(other.vars),
            mutable_vars: self.mutable_vars.union(other.mutable_vars),
        }
    }

    fn intersection(self, other: Self) -> Self {
        Self {
            vars: self.vars.intersection(other.vars),
            mutable_vars: self.mutable_vars.union(other.mutable_vars),
        }
    }

    fn change(self, other: Self) -> Self {
        Self {
            vars: other.vars,
            mutable_vars: self.mutable_vars.union(other.mutable_vars),
        }
    }
}

fn sig_args(sig: &FnValue) -> Vec<Typ> {
    match sig {
        FnValue::Local(sig) => sig.args.clone().into_iter().map(|(_, (x, _))| x).collect(),
        FnValue::External(sig) => sig.args.clone(),
        FnValue::ExternalNotInHacspec(_) => panic!("should not happen"),
    }
}

fn sig_ret(sig: &FnValue) -> BaseTyp {
    match sig {
        FnValue::Local(sig) => sig.ret.0.clone(),
        FnValue::External(sig) => sig.ret.clone(),
        FnValue::ExternalNotInHacspec(_) => panic!("should not happen"),
    }
}

fn sig_mut_vars(sig: &FnValue) -> ScopeMutableVars {
    match sig {
        FnValue::Local(sig) => sig.mutable_vars.clone(),
        FnValue::External(_) => ScopeMutableVars::new(),
        FnValue::ExternalNotInHacspec(_) => panic!("should not happen"),
    }
}

fn find_func(
    sess: &Session,
    key1: &FnKey,
    top_level_context: &TopLevelContext,
    span: &RustspecSpan,
) -> TypecheckingResult<(FnValue, TypeVarCtx)> {
    let key1 = &match key1 {
        FnKey::Independent(_) => key1.clone(),
        FnKey::Impl(t1, n1) => FnKey::Impl(dealias_type(t1.clone(), top_level_context), n1.clone()),
    };
    let candidates = top_level_context.functions.clone();
    let mut has_err = false;
    let candidates: Vec<_> = candidates
        .iter()
        .filter_map(|(key2, sig)| match (key1, key2) {
            (FnKey::Independent(n1), FnKey::Independent(n2)) => match (n1, n2) {
                (TopLevelIdent { string: n1, .. }, TopLevelIdent { string: n2, .. }) => {
                    if n1 == n2 {
                        Some((HashMap::new(), sig))
                    } else {
                        None
                    }
                }
            },
            (FnKey::Impl(t1, n1), FnKey::Impl(t2, n2)) => {
                let unification: TypecheckingResult<Option<TypeVarCtx>> = unify_types(
                    sess,
                    &(
                        (Borrowing::Consumed, span.clone()),
                        (t1.clone(), span.clone()),
                    ),
                    &(
                        (Borrowing::Consumed, span.clone()),
                        (dealias_type(t2.clone(), top_level_context), span.clone()),
                    ),
                    &HashMap::new(),
                    top_level_context,
                );
                match unification {
                    Ok(Some(new_typ_ctx)) => match (n1, n2) {
                        (TopLevelIdent { string: n1, .. }, TopLevelIdent { string: n2, .. }) => {
                            if n1 == n2 {
                                Some((new_typ_ctx, sig))
                            } else {
                                None
                            }
                        }
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
    // TODO: figure out why we need this
    // https://github.com/hacspec/hacspec/issues/194
    let candidates = if candidates.iter().all(|(_, candidate)| match candidate {
        FnValue::ExternalNotInHacspec(_) => true,
        _ => false,
    }) {
        // If all candidates are not in hacspec we return one
        candidates
    } else {
        // If not we discard the not in hacspec candidates and return
        // one in hacspec
        candidates
            .into_iter()
            .filter(|(_, candidate)| match candidate {
                FnValue::ExternalNotInHacspec(_) => false,
                _ => true,
            })
            .collect()
    };

    for (typ_ctx, sig) in candidates {
        return Ok((sig.clone(), typ_ctx));
    }
    Err(())
}

fn find_typ(
    x: &Ident,
    var_context: &VarContext,
    top_level_context: &TopLevelContext,
) -> Option<Typ> {
    log::trace!("find_typ {}", x);
    match x {
        Ident::Unresolved(_) => panic!("name resolution should have already happened"),
        Ident::TopLevel(name) => top_level_context.consts.get(name).map(|(t, span)| {
            (
                (Borrowing::Consumed, span.clone()),
                (t.clone(), span.clone()),
            )
        }),
        Ident::Local(LocalIdent {
            name: _,
            id,
            mutable: _,
        }) => var_context.vars.get(id).map(|x| x.0.clone()),
    }
}

fn remove_var(x: &Ident, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Local(LocalIdent {
            id,
            name: _,
            mutable: _,
        }) => VarContext {
            vars: var_context.vars.without(id),
            mutable_vars: var_context.clone().mutable_vars,
        },
        _ => panic!("trying to lookup in the var context a non-local id"),
    }
}

fn add_var(x: &Ident, typ: &Typ, var_context: &VarContext) -> VarContext {
    log::trace!("add_var {} of type {:?}", x, typ);
    match x {
        Ident::Local(LocalIdent { id, name, mutable }) => VarContext {
            vars: var_context
                .vars
                .update(id.clone(), (typ.clone(), name.clone(), mutable.clone())),
            mutable_vars: if mutable.clone() {
                var_context
                    .mutable_vars
                    .update(id.clone(), (typ.clone(), name.clone(), false))
            } else {
                var_context.mutable_vars.clone()
            },
        },
        _ => panic!("trying to lookup in the var context a non-local id"),
    }
}

fn get_literal_type(l: &Literal) -> BaseTyp {
    match l {
        Literal::Unit => UnitTyp,
        Literal::Bool(_) => BaseTyp::Bool,
        Literal::Int128(_) => BaseTyp::Int128,
        Literal::UInt128(_) => BaseTyp::UInt128,
        Literal::Int64(_) => BaseTyp::Int64,
        Literal::UInt64(_) => BaseTyp::UInt64,
        Literal::Int32(_) => BaseTyp::Int32,
        Literal::UInt32(_) => BaseTyp::UInt32,
        Literal::Int16(_) => BaseTyp::Int16,
        Literal::UInt16(_) => BaseTyp::UInt16,
        Literal::Int8(_) => BaseTyp::Int8,
        Literal::UInt8(_) => BaseTyp::UInt8,
        Literal::Usize(_) => BaseTyp::Usize,
        Literal::Isize(_) => BaseTyp::Isize,
        Literal::Str(_) => BaseTyp::Str,
    }
}

fn typecheck_arm(
    sess: &Session,
    pat: &Spanned<Pattern>,
    pat_typ: &Typ,
    e @ (_, e_span): &Spanned<Expression>,
    mut e_typ: &mut Option<Typ>,
    func_return_type: &Option<&Spanned<BaseTyp>>,
    var_context: &VarContext,
    mut acc_var_context: &mut VarContext,
    top_ctx: &TopLevelContext,
) -> Result<(Spanned<Pattern>, Spanned<Expression>), ()> {
    let pat_var_context = typecheck_pattern(sess, pat, pat_typ, top_ctx)?;
    let (e, e_typ_inferred, var_context) = typecheck_expression(
        sess,
        e,
        func_return_type,
        top_ctx,
        &var_context.clone().union(pat_var_context),
    )?;
    *acc_var_context = acc_var_context.clone().intersection(var_context.clone());
    match &e_typ {
        None => *e_typ = Some(e_typ_inferred),
        Some(out_typ) => {
            unify_types_default_error_message(
                sess,
                &e_typ_inferred,
                out_typ,
                &HashMap::new(),
                top_ctx,
            )?;
        }
    }
    Ok((pat.clone(), (e, e_span.clone())))
}

pub type TypecheckingResult<T> = Result<T, ()>;

fn typecheck_expression(
    sess: &Session,
    (e, span): &Spanned<Expression>,
    func_return_type: &Option<&Spanned<BaseTyp>>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
) -> TypecheckingResult<(Expression, Typ, VarContext)> {
    log::trace!("typecheck_expression {:?} ({:?})", e, span);
    #[cfg(feature = "dev")]
    log::trace!("   {:?}", backtrace::Backtrace::new());
    match e {
        Expression::MonadicLet(..) => {
            // TODO: eliminiate this `panic!` with nicer types (See issue #303)
            panic!("Expression::MonadicLet should be elaborated only after typechecking")
        }
        Expression::QuestionMark(qe, ..) => {
            if let &Some(return_typ) = func_return_type {
                let (_, qe_span) = **qe;
                let (qe, typ, var_context) = typecheck_expression(
                    sess,
                    qe,
                    func_return_type,
                    top_level_context,
                    var_context,
                )?;
                let carrier = typ.clone().1 .0.try_into().unwrap();
                let typ = typecheck_question_mark(
                    sess,
                    true,
                    typ,
                    return_typ,
                    qe_span,
                    top_level_context,
                )?;
                Ok((
                    Expression::QuestionMark(Box::new((qe, qe_span)), Some(carrier)),
                    typ,
                    var_context,
                ))
            } else {
                sess.span_rustspec_err(
                    *span,
                    "found a question mark while typechecking an item which is not a function (i.e. a constant declaration)",
                );
                Err(())
            }
        }
        Expression::Tuple(args) => {
            let mut var_context = var_context.clone();
            let new_arg_and_typ = args
                .iter()
                .map(|arg| {
                    let (new_arg, ((arg_typ_borrowing, _), arg_typ), new_var_context) =
                        typecheck_expression(
                            sess,
                            arg,
                            func_return_type,
                            top_level_context,
                            &var_context,
                        )?;
                    var_context = var_context.clone().change(new_var_context.clone());
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

            let new_arg_and_typ = check_vec(new_arg_and_typ)?;
            let (new_args, typ_args): (Vec<_>, Vec<_>) = new_arg_and_typ.into_iter().unzip();

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
            log::trace!("    named {}", id);
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
                    log::trace!("    t {:?}", t);
                    // This is where linearity kicks in
                    if let Borrowing::Consumed = (t.0).0 {
                        if is_copy(&(t.1).0, top_level_context) {
                            log::trace!("    Copied - new path: {:?}", new_path);
                            Ok((new_path, t.clone(), var_context.clone()))
                        } else {
                            log::trace!("    Consumed - new path: {:?}", new_path);
                            let new_var_context = remove_var(&id, var_context);
                            Ok((new_path, t.clone(), new_var_context))
                        }
                    } else {
                        log::trace!("    Just cloned - new path: {:?}", new_path);
                        Ok((new_path, t.clone(), var_context.clone()))
                    }
                }
            }
        }
        Expression::MatchWith(arg @ box (_, arg_span), arms) => {
            let (arg, t_arg, intermediate_var_context) =
                typecheck_expression(sess, arg, func_return_type, top_level_context, &var_context)?;
            let mut acc_var_context = intermediate_var_context.clone();
            let mut out_typ = None;

            // Typecheck each match arm
            let arms = arms
                .into_iter()
                .map(|(arm_pattern, arm_exp)| {
                    typecheck_arm(
                        sess,
                        arm_pattern,
                        &t_arg,
                        arm_exp,
                        &mut out_typ,
                        func_return_type,
                        &intermediate_var_context,
                        &mut acc_var_context,
                        top_level_context,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((
                Expression::MatchWith(Box::new((arg, arg_span.clone())), arms),
                out_typ.unwrap(),
                acc_var_context,
            ))
        }
        Expression::EnumInject(enum_ty, case_name, payload) => {
            let (enum_cases, enum_name, enum_args) = match enum_ty {
                BaseTyp::Named(enum_name, args) => {
                    match top_level_context.typ_dict.get(&enum_name.0) {
                        Some((
                            ((Borrowing::Consumed, _), (BaseTyp::Enum(cases, type_args), _)),
                            DictEntry::Enum,
                        )) => {
                            if (args.is_none() && type_args.len() != 0)
                                || (args.is_some()
                                    && args.as_ref().unwrap().len() != type_args.len())
                            {
                                sess.span_rustspec_err(
                                    enum_name.1.clone(),
                                    format!(
                                        "wrong number of type arguments: got {:?}, expected {:?}",
                                        args, type_args
                                    )
                                    .as_str(),
                                );
                                return Err(());
                            }
                            // No need to unify the type_args here
                            (cases, enum_name, args)
                        }
                        _ => {
                            sess.span_rustspec_err(enum_name.1.clone(), "enum not found");
                            return Err(());
                        }
                    }
                }
                _ => panic!("should not happen"),
            };
            let case_typ = match enum_cases
                .iter()
                .find(|((case_name_candidate, _), _)| case_name_candidate == &case_name.0)
            {
                Some((_, case_typ)) => case_typ,
                _ => {
                    sess.span_rustspec_err(
                        case_name.1.clone(),
                        format!("enum case not found for {}", enum_name.0).as_str(),
                    );
                    return Err(());
                }
            };
            let mut var_context = var_context.clone();
            let new_payload = match (case_typ, payload) {
                (None, None) => None,
                (Some(case_typ), Some((payload, payload_span))) => {
                    let (new_payload, payload_type, new_var_context) = typecheck_expression(
                        sess,
                        &(*payload.clone(), payload_span.clone()),
                        func_return_type,
                        top_level_context,
                        &var_context,
                    )?;
                    var_context = new_var_context;
                    unify_types_default_error_message(
                        sess,
                        &((Borrowing::Consumed, case_name.1.clone()), case_typ.clone()),
                        &payload_type,
                        &HashMap::new(),
                        top_level_context,
                    )?;
                    Some((Box::new(new_payload), payload_span.clone()))
                }
                _ => {
                    sess.span_rustspec_err(case_name.1.clone(), "incorrect payload");
                    return Err(());
                }
            };
            Ok((
                Expression::EnumInject(enum_ty.clone(), case_name.clone(), new_payload),
                (
                    (Borrowing::Consumed, span.clone()),
                    (
                        BaseTyp::Named(enum_name.clone(), enum_args.clone()),
                        span.clone(),
                    ),
                ),
                var_context,
            ))
        }
        Expression::InlineConditional(cond, e_t, e_f) => {
            let (new_cond, t_cond, var_context) = typecheck_expression(
                sess,
                cond,
                func_return_type,
                top_level_context,
                &var_context,
            )?;
            unify_types_default_error_message(
                sess,
                &t_cond,
                &(
                    (Borrowing::Consumed, (t_cond.0).1),
                    (BaseTyp::Bool, (t_cond.1).1),
                ),
                &HashMap::new(),
                top_level_context,
            )?;
            let (new_e_t, t_e_t, var_context_true_branch) =
                typecheck_expression(sess, e_t, func_return_type, top_level_context, &var_context)?;
            let (new_e_f, t_e_f, var_context_false_branch) =
                typecheck_expression(sess, e_f, func_return_type, top_level_context, &var_context)?;
            let final_var_context = var_context
                .clone()
                .intersection(var_context_true_branch)
                .intersection(var_context_false_branch);
            unify_types_default_error_message(
                sess,
                &t_e_t,
                &t_e_f,
                &HashMap::new(),
                top_level_context,
            )?;
            Ok((
                Expression::InlineConditional(
                    Box::new((new_cond, cond.1.clone())),
                    Box::new((new_e_t, e_t.1.clone())),
                    Box::new((new_e_f, e_f.1.clone())),
                ),
                t_e_t,
                final_var_context,
            ))
        }
        Expression::Binary((op, op_span), e1, e2, _) => {
            let (new_e1, t1, var_context) =
                typecheck_expression(sess, e1, func_return_type, top_level_context, var_context)?;
            let (new_e2, t2, var_context) =
                typecheck_expression(sess, e2, func_return_type, top_level_context, &var_context)?;
            match op {
                BinOpKind::Shl | BinOpKind::Shr => match &(t2.1).0 {
                    BaseTyp::UInt32 | BaseTyp::Usize => {
                        if is_numeric(&t1, top_level_context) {
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
                                "the shifting amount has to be an u32 or an usize, found type {}{}",
                                (t2.0).0,
                                (t2.1).0
                            )
                            .as_str(),
                        );
                        Err(())
                    }
                },
                _ => {
                    if unify_types(sess, &t1, &t2, &HashMap::new(), top_level_context)?.is_none() {
                        sess.span_rustspec_err(
                            *span,
                            format!(
                                "wrong types of binary operators, left is {}{} while right is {}{}",
                                (t1.0).0,
                                (t1.1).0,
                                (t2.0).0,
                                (t2.1).0
                            )
                            .as_str(),
                        );
                        Err(())
                    } else {
                        if is_numeric(&t1, top_level_context)
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
                            if is_bool(&t1, top_level_context)
                                && (match op {
                                    BinOpKind::And | BinOpKind::Or => true,
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
                                    ((Borrowing::Consumed, (t1.0).1), (BaseTyp::Bool, (t1.1).1)),
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
        }
        Expression::Unary(op, e1, _) => {
            let (new_e1, e1_typ, new_var_context) =
                typecheck_expression(sess, e1, func_return_type, top_level_context, var_context)?;
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
        Expression::Lit(lit) => Ok((
            e.clone(),
            (
                (Borrowing::Consumed, span.clone()),
                (get_literal_type(lit), span.clone()),
            ),
            var_context.clone(),
        )),
        Expression::NewArray(array_type, _, elements) => {
            match array_type {
                Some(array_type) => {
                    let (array_len, (cell_type, cell_type_span)) = is_array(
                        sess,
                        &(
                            (Borrowing::Consumed, array_type.1.clone()),
                            (
                                BaseTyp::Named(array_type.clone(), None),
                                array_type.1.clone(),
                            ),
                        ),
                        top_level_context,
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
                    };
                    let mut var_context = var_context.clone();
                    let new_elements = check_vec(
                        elements
                            .iter()
                            .map(|element| {
                                let (new_element, element_typ, new_var_context) =
                                    typecheck_expression(
                                        sess,
                                        element,
                                        func_return_type,
                                        top_level_context,
                                        &var_context,
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
                                    top_level_context,
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
                    let new_array_typ = (
                        (Borrowing::Consumed, array_type.1.clone()),
                        (
                            BaseTyp::Named(array_type.clone(), None),
                            array_type.1.clone(),
                        ),
                    );
                    Ok((
                        Expression::NewArray(
                            Some(array_type.clone()),
                            Some(cell_type),
                            new_elements,
                        ),
                        new_array_typ,
                        var_context,
                    ))
                }
                None => {
                    let mut cell_type: Option<(BaseTyp, RustspecSpan)> = None;
                    let mut var_context = var_context.clone();
                    let new_elements = check_vec(
                        elements
                            .iter()
                            .map(|element| {
                                let (new_element, element_typ, new_var_context) =
                                    typecheck_expression(
                                        sess,
                                        element,
                                        func_return_type,
                                        top_level_context,
                                        &var_context,
                                    )?;
                                var_context = new_var_context;
                                match &cell_type {
                                    Some((cell_type, cell_type_span)) => {
                                        match unify_types(
                                            sess,
                                            &(
                                                (Borrowing::Consumed, cell_type_span.clone()),
                                                (cell_type.clone(), cell_type_span.clone()),
                                            ),
                                            &element_typ,
                                            &HashMap::new(),
                                            top_level_context,
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
                                    }
                                    None => match element_typ.0 .0 {
                                        Borrowing::Consumed => {
                                            cell_type = Some(element_typ.1);
                                            Ok(element.clone())
                                        }
                                        Borrowing::Borrowed => {
                                            sess.span_rustspec_err(
                                                (element_typ.0).1,
                                                "cannot insert references in a Seq",
                                            );
                                            Err(())
                                        }
                                    },
                                }
                            })
                            .collect(),
                    )?;
                    let cell_type = match cell_type {
                        Some(x) => x,
                        None => {
                            sess.span_rustspec_err(
                                span.clone(),
                                "use Seq::new() to create an empty sequence instead",
                            );
                            return Err(());
                        }
                    };
                    Ok((
                        Expression::NewArray(None, Some(cell_type.0.clone()), new_elements),
                        (
                            (Borrowing::Consumed, span.clone()),
                            (BaseTyp::Seq(Box::new(cell_type)), span.clone()),
                        ),
                        var_context,
                    ))
                }
            }
        }
        Expression::ArrayIndex((x, x_span), e2, _) => {
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
            let (new_e2, t2, var_context) =
                typecheck_expression(sess, e2, func_return_type, top_level_context, &var_context)?;
            let (_, (cell_t, cell_t_span)) = is_array(sess, &t1, top_level_context, x_span)?;
            // We ignore t1.0 because we can read from both consumed and borrowed array types
            if let Borrowing::Borrowed = (t2.0).0 {
                sess.span_rustspec_err(e2.1, "cannot index array with a borrowed type");
                return Err(());
            }
            if is_index(&(t2.1).0, top_level_context) {
                Ok((
                    Expression::ArrayIndex(
                        (x.clone(), x_span.clone()),
                        Box::new((new_e2, e2.1.clone())),
                        Some(t1.clone()),
                    ),
                    (
                        (Borrowing::Consumed, (t1.0).1),
                        (cell_t.clone(), cell_t_span.clone()),
                    ),
                    var_context,
                ))
            } else {
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
        Expression::FuncCall(prefix, name, args, _arg_types) => {
            let (f_sig, typ_var_ctx) = find_func(
                sess,
                &match prefix {
                    None => FnKey::Independent(name.0.clone()),
                    Some((prefix, _)) => FnKey::Impl(prefix.clone(), name.0.clone()),
                },
                top_level_context,
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
            let mut new_arg_types = Vec::new();
            for (sig_t, ((arg, arg_span), (arg_borrow, arg_borrow_span))) in
                sig_args.iter().zip(args)
            {
                let (new_arg, arg_t, new_var_context) = typecheck_expression(
                    sess,
                    &(arg.clone(), arg_span.clone()),
                    func_return_type,
                    top_level_context,
                    &var_context,
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
                        match arg {
                            Expression::Named(_) => {
                                // If the argument is a variable, then the consumed
                                // variables are actually
                                // not consumed so we don't update the var context
                            }
                            _ => {
                                // in the case of a tuple or anything else
                                // you want to register all the moves
                                // that have happened
                                var_context = new_var_context;
                            }
                        }
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
                new_arg_types.push(new_arg_t.1 .0.clone());
                match unify_types(sess, &new_arg_t, sig_t, &typ_var_ctx, top_level_context)? {
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
            let ret_ty =
                match bind_variable_type(sess, &(ret_ty.clone(), span.clone()), &typ_var_ctx) {
                    Ok(ret_ty) => ret_ty,
                    Err(_) => {
                        sess.span_rustspec_err(
                            name.1,
                            "A type variable cannot be unified, please provide \
                                the type parameters for this function",
                        );
                        return Err(());
                    }
                };
            let external_mut_vars = sig_mut_vars(&f_sig);
            for (x, y) in external_mut_vars
                .local_vars
                .clone()
                .union(external_mut_vars.external_vars)
            {
                match (x, y) {
                    (
                        Ident::Local(LocalIdent {
                            id,
                            name,
                            mutable: _,
                        }),
                        Some(var),
                    ) => {
                        // TODO: mutable should always be true
                        var_context.mutable_vars =
                            var_context.mutable_vars.update(id, (var, name, true))
                    }
                    _ => (),
                }
            }
            Ok((
                Expression::FuncCall(prefix.clone(), name.clone(), new_args, Some(new_arg_types)),
                (
                    (Borrowing::Consumed, name.1.clone()),
                    (ret_ty, name.1.clone()),
                ),
                var_context,
            ))
        }
        Expression::MethodCall(sel, _, (f, f_span), orig_args, _arg_types) => {
            let (sel, sel_borrow) = sel.as_ref();
            let mut var_context = var_context.clone();
            // We omit to take the new var context because it will be retypechecked later, this
            // is just to determine wich type the method belongs to
            let (_, sel_typ, _) = typecheck_expression(
                sess,
                &sel,
                func_return_type,
                top_level_context,
                &var_context,
            )?;
            let (f_sig, typ_var_ctx) = find_func(
                sess,
                &FnKey::Impl((sel_typ.1).0.clone(), f.clone()),
                top_level_context,
                f_span,
            )?;
            let mut typ_var_ctx = typ_var_ctx;
            if let FnValue::ExternalNotInHacspec(sig_str) = f_sig {
                sess.span_rustspec_err(
                    *f_span,
                    format!(
                        "function {}::{} is known but its signature is not in Hacspec: {}",
                        (sel_typ.1).0,
                        f,
                        sig_str
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
            let mut new_arg_types = Vec::new();
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
                    func_return_type,
                    top_level_context,
                    &var_context,
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
                        match arg {
                            Expression::Named(_) => {
                                // If the argument is a variable, then the consumed
                                // variables are actually
                                // not consumed so we don't update the var context
                            }
                            _ => {
                                // in the case of a tuple or anything else
                                // you want to register all the moves
                                // that have happened
                                var_context = new_var_context;
                            }
                        }
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
                new_arg_types.push((new_arg_t.1).0.clone());
                match unify_types(sess, &new_arg_t, sig_t, &typ_var_ctx, top_level_context)? {
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
            new_arg_types = new_arg_types[1..].to_vec();
            let ret_ty = sig_ret(&f_sig);
            let ret_ty = bind_variable_type(sess, &(ret_ty.clone(), span.clone()), &typ_var_ctx)?;
            let external_mut_vars = sig_mut_vars(&f_sig);
            for (x, y) in external_mut_vars
                .local_vars
                .clone()
                .union(external_mut_vars.external_vars)
            {
                match (x, y) {
                    (
                        Ident::Local(LocalIdent {
                            id,
                            name,
                            mutable: _,
                        }),
                        Some(var),
                    ) => {
                        // TODO: mutable should always be true here
                        var_context.mutable_vars =
                            var_context.mutable_vars.update(id, (var, name, true))
                    }
                    _ => (),
                }
            }
            Ok((
                Expression::MethodCall(
                    Box::new(new_sel),
                    Some(sel_typ),
                    (f.clone(), f_span.clone()),
                    new_args,
                    Some(new_arg_types),
                ),
                (
                    (Borrowing::Consumed, f_span.clone()),
                    (ret_ty, f_span.clone()),
                ),
                var_context,
            ))
        }
        Expression::LetBinding(
            pat,
            typ_annot,
            exp @ box (_, exp_span),
            body @ box (_, body_span),
        ) => {
            let (exp, t_exp, intermediate_var_context) =
                typecheck_expression(sess, exp, func_return_type, top_level_context, &var_context)?;
            let mut acc_var_context = intermediate_var_context.clone();
            let mut out_typ = typ_annot.clone().map(|(ty, _)| ty);

            let (pat, body) = typecheck_arm(
                sess,
                pat,
                &t_exp,
                body,
                &mut out_typ,
                func_return_type,
                &intermediate_var_context,
                &mut acc_var_context,
                top_level_context,
            )?;

            Ok((
                Expression::LetBinding(
                    pat,
                    typ_annot.clone(),
                    box (exp, exp_span.clone()),
                    box body,
                ),
                out_typ.unwrap(),
                acc_var_context,
            ))
        }
        Expression::IntegerCasting(e1, t1, _) => {
            log::trace!("Expression::IntegerCasting {:?} - {:?}", e1, t1);
            let (new_e1, e1_typ, var_context) =
                typecheck_expression(sess, e1, func_return_type, top_level_context, var_context)?;
            if (e1_typ.0).0 == Borrowing::Borrowed {
                sess.span_rustspec_err(e1.1.clone(), "cannot cast borrowed expression");
                return Err(());
            }
            log::trace!("   e1 type {:?}", e1_typ);
            if !is_castable_integer(&(e1_typ.1).0, top_level_context) {
                sess.span_rustspec_err(
                    e1.1.clone(),
                    format!(
                        "this expression of type {}{} cannot be casted",
                        (e1_typ.0).0,
                        (e1_typ.1).0
                    )
                    .as_str(),
                );
                return Err(());
            }
            if !is_castable_integer(&t1.0, top_level_context) {
                sess.span_rustspec_err(e1.1.clone(), "impossible to cast to this type");
                return Err(());
            }
            if !is_safe_casting(&(e1_typ.1).0, &t1.0) {
                sess.span_rustspec_warn(
                    span.clone(),
                    format!(
                        "casting from {} to {} is not safe (i.e it can lead to overflow)",
                        &e1_typ.1 .0, &t1.0
                    )
                    .as_str(),
                );
            }
            let expr = Expression::IntegerCasting(
                Box::new((new_e1, e1.1.clone())),
                t1.clone(),
                Some((e1_typ.1).0.clone()),
            );
            log::trace!("   casting expression {:?}", expr);
            Ok((
                expr,
                ((Borrowing::Consumed, t1.1.clone()), t1.clone()),
                var_context,
            ))
        }
    }
}

fn translate_var_context_to_mut_vars(var_context: VarContext) -> ScopeMutableVars {
    let mut mut_vars = ScopeMutableVars::new();

    for (var_id, (var, var_name, is_external)) in var_context.clone().mutable_vars {
        let mut_var = (
            Ident::Local(LocalIdent {
                id: var_id.clone(),
                name: var_name.clone(),
                mutable: true,
            }),
            Some(var.clone()),
        );

        if is_external {
            mut_vars.push_external(mut_var);
        } else {
            mut_vars.push(mut_var);
        }
    }

    mut_vars
}

fn typecheck_pattern(
    sess: &Session,
    (pat, pat_span): &Spanned<Pattern>,
    (borrowing_typ, typ): &Typ,
    top_ctx: &TopLevelContext,
) -> TypecheckingResult<VarContext> {
    match &typ.0 {
        BaseTyp::Named((name, _), None) => match top_ctx.typ_dict.get(name) {
            Some((((Borrowing::Consumed, _), (new_ty, _)), DictEntry::Alias)) => {
                return typecheck_pattern(
                    sess,
                    &(pat.clone(), pat_span.clone()),
                    &(borrowing_typ.clone(), (new_ty.clone(), typ.1.clone())),
                    top_ctx,
                )
            }
            _ => (),
        },
        _ => (),
    };
    match (pat, &typ.0) {
        (
            Pattern::EnumCase(ty_name, (pat_enum_name, _), inner_pat),
            BaseTyp::Named((typ_name, _), case_type_annotations),
        ) => match top_ctx.typ_dict.get(typ_name) {
            Some((
                ((Borrowing::Consumed, _), (BaseTyp::Enum(cases, type_args), cases_span)),
                DictEntry::Enum,
            )) => {
                let case_typ =
		// Among all constructors [cases] of the enum we're matching against, find the
		// one named [pat_enum_name]
		    cases.into_iter().find(
			|((name,_),_)| name.string == pat_enum_name.string
		    ).unwrap().1.as_ref()
		// The constructor we're matching against has [length(type_args)] generic type
		// arguments, a vector of [TypVar]. We substitutes those [type_args] into their
		// respective [case_type_annotations].
		    .map(|case_typ| bind_variable_type(
			sess, case_typ,
			&type_args.iter() // build a var context (a HashMap)
			    .map(|type_arg| type_arg.clone())
			    .zip(case_type_annotations.iter().flatten().map(|t| t.0.clone()))
			    .collect()
		    ).ok()).flatten();

                let failure = |message| {
                    sess.span_rustspec_err(
                        *pat_span,
                        format!(
                            "this pattern is matching the enum {} with {}",
                            pat_enum_name, message
                        )
                        .as_str(),
                    );
                    Err(())
                };

                match (inner_pat, case_typ) {
                    (Some(inner_pat), Some(case_typ)) => typecheck_pattern(
                        sess,
                        inner_pat,
                        &(
                            borrowing_typ.clone(), // This propagates the borrowing down the enum
                            (case_typ, *cases_span),
                        ),
                        top_ctx,
                    ),
                    (Some(_), _) => failure("one case but no payload"),
                    (_, Some(_)) => failure("an unexpected payload"),
                    _ => Ok(VarContext::new()),
                }
            }
            _ => {
                sess.span_rustspec_err(
                    *pat_span,
                    format!(
                        "let-binding pattern expected a {} struct but the type is {}",
                        pat_enum_name, typ.0
                    )
                    .as_str(),
                );
                Err(())
            }
        },
        (Pattern::EnumCase(ty_name, name, _), _) => {
            sess.span_rustspec_err(
                *pat_span,
                format!(
                    "let-binding pattern expected a {} struct but the type is {}",
                    name.0, typ.0
                )
                .as_str(),
            );
            Err(())
        }
        (Pattern::Tuple(pat_args), BaseTyp::Tuple(ref typ_args)) => {
            if pat_args.len() != typ_args.len() {
                sess.span_rustspec_err(*pat_span,
                    format!("let-binding tuple pattern has {} variables but {} were expected from the type",
                     pat_args.len(),
                     typ_args.len()).as_str()
                )
            };
            let acc_var = pat_args.iter().zip(typ_args.iter()).fold(
                Ok(VarContext::new()),
                |acc, (pat_arg, typ_arg)| {
                    let acc_var = acc?;
                    let sub_var_context = typecheck_pattern(
                        sess,
                        pat_arg,
                        &(borrowing_typ.clone(), typ_arg.clone()),
                        top_ctx,
                    )?;
                    Ok(acc_var.union(sub_var_context))
                },
            )?;
            Ok(acc_var)
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
        (Pattern::WildCard, _) => Ok(VarContext::new()),
        (Pattern::LiteralPat(l), t) => {
            if get_literal_type(l) == t.clone() {
                Ok(VarContext::new())
            } else {
                Err(())
            }
        }
        (Pattern::IdentPat(x, m), _) => {
            let (id, name) = match &x {
                Ident::Local(LocalIdent {
                    id,
                    name,
                    mutable: _,
                }) => (id.clone(), name.clone()),
                _ => panic!("should not happen"),
            };
            Ok(VarContext::unit(
                id,
                (
                    (borrowing_typ.clone(), typ.clone()),
                    name.clone(),
                    m.clone(),
                ),
                false,
            ))
        }
    }
}

fn var_set_to_tuple(vars: &VarSet, span: &RustspecSpan, var_context: &VarContext) -> Statement {
    if vars.0.len() > 0 {
        Statement::ReturnExp(
            Expression::Tuple(
                vars.0
                    .iter()
                    .sorted()
                    .map(|i| (Expression::Named(Ident::Local(i.clone())), span.clone()))
                    .collect(),
            ),
            (vars
                .0
                .iter()
                .sorted()
                .map(|i| var_context.vars.get(&i.clone().id).map(|(x, _, _)| x))
                .collect::<Option<Vec<_>>>())
            .map(|tup| {
                (
                    (Borrowing::Consumed, span.clone()),
                    (
                        BaseTyp::Tuple(tup.into_iter().map(|(_, x)| x.clone()).collect()),
                        span.clone(),
                    ),
                )
            }),
        )
    } else {
        Statement::ReturnExp(
            Expression::Lit(Literal::Unit),
            Some(((Borrowing::Consumed, span.clone()), (UnitTyp, span.clone()))),
        )
    }
}

fn dealias_type(ty: BaseTyp, top_level_context: &TopLevelContext) -> BaseTyp {
    log::trace!("dealias_type {:?}", ty);
    match &ty {
        BaseTyp::Named((name, _), None) => match top_level_context.typ_dict.get(name) {
            Some((((Borrowing::Consumed, _), (aliased_ty, _)), DictEntry::Alias)) => {
                dealias_type(aliased_ty.clone(), top_level_context)
            }
            _ => ty,
        },
        _ => ty,
    }
}

impl Into<BaseTyp> for CarrierTyp {
    fn into(self) -> BaseTyp {
        fn mk(name: &str, args: Vec<Spanned<BaseTyp>>) -> BaseTyp {
            BaseTyp::Named(
                (
                    TopLevelIdent {
                        string: name.to_string(),
                        kind: TopLevelIdentKind::EnumConstructor,
                    },
                    DUMMY_SP.into(),
                ),
                Some(args),
            )
        }
        match self {
            CarrierTyp::Option(t1) => mk("Option", vec![t1]),
            CarrierTyp::Result(t1, t2) => mk("Result", vec![t1, t2]),
        }
    }
}

impl TryInto<CarrierTyp> for BaseTyp {
    type Error = ();
    fn try_into(self) -> Result<CarrierTyp, Self::Error> {
        if let BaseTyp::Named((TopLevelIdent { string: name, .. }, _), Some(args)) = self {
            match (name.as_str(), args.as_slice()) {
                ("Option", [t1]) => Ok(CarrierTyp::Option(t1.clone())),
                ("Result", [t1, t2]) => Ok(CarrierTyp::Result(t1.clone(), t2.clone())),
                _ => Err(()),
            }
        } else {
            Err(())
        }
    }
}

/// Given a `carrier` and a `payload`, `pure_carrier(carrier,
/// payload)` returns `payload` in the monad associated with
/// `carrier`, i.e., crafts the term `return 〚payload〛`.
pub fn pure_carrier(carrier: CarrierTyp, payload: Spanned<Expression>) -> Spanned<Expression> {
    (
        Expression::EnumInject(
            carrier.clone().into(),
            (
                TopLevelIdent {
                    string: (match carrier.clone() {
                        CarrierTyp::Option(..) => "Some",
                        CarrierTyp::Result(..) => "Ok",
                    })
                    .to_string(),
                    kind: TopLevelIdentKind::EnumConstructor,
                },
                DUMMY_SP.into(),
            ),
            Some((Box::new(payload.0), payload.1)),
        ),
        payload.1,
    )
}

// This function returns the type in the OK branch of the result return type
// if there is a question mark
fn typecheck_question_mark(
    sess: &Session,
    question_mark: bool,
    expr_typ: Typ,
    return_typ: &Spanned<BaseTyp>,
    expr_span: RustspecSpan,
    top_level_context: &TopLevelContext,
) -> TypecheckingResult<Typ> {
    let expr_typ = (
        expr_typ.0,
        (
            dealias_type(expr_typ.1 .0, top_level_context),
            expr_typ.1 .1,
        ),
    );
    let return_typ = &(
        dealias_type(return_typ.0.clone(), top_level_context),
        return_typ.1.clone(),
    );

    if question_mark {
        let expr_carrier: Result<CarrierTyp, _> = match expr_typ.clone() {
            ((Borrowing::Consumed, _), (expr_typ, _)) => expr_typ.try_into(),
            _ => Err(()),
        };
        let return_carrier: Result<CarrierTyp, _> = return_typ.0.clone().try_into();

        match (expr_carrier, return_carrier) {
            (Err(..), _) => {
                sess.span_rustspec_err(
                    expr_span,
                    format!(
                        "expected a result type for this \
			 expression ending with a question mark, got {}{}",
                        (expr_typ.0).0,
                        (expr_typ.1).0
                    )
                    .as_str(),
                );
                Err(())
            }
            (Ok(expr_carrier), Ok(return_carrier))
                if carrier_kind(expr_carrier.clone()) == carrier_kind(return_carrier.clone()) =>
            {
                let ok_type = carrier_payload(expr_carrier.clone());
                // TODO: previously, type unification was ran for T in
                // case of a [Result<_,T>]. Feels like either it was
                // unnecessary, or we should check unification
                // succeeds for every type involved in the carrier
                // (i.e. [A] and [B] for [Result<A,B>] and [A] for
                // [Option<A>]).
                Ok(((Borrowing::Consumed, ok_type.1), ok_type))
            }
            (Ok(expr_carrier), _) => {
                sess.span_rustspec_err(
                    return_typ.1,
                    format!(
                        "expected a {:?} type for this \
			 return type because of a question mark in the function, got {}",
                        carrier_kind(expr_carrier),
                        return_typ.0,
                    )
                    .as_str(),
                );
                Err(())
            }
        }
    } else {
        Ok(expr_typ)
    }
}

fn early_return_type_from_return_type(
    top_level_context: &TopLevelContext,
    return_typ: BaseTyp,
) -> Fillable<CarrierTyp> {
    match dealias_type(return_typ, top_level_context) {
        BaseTyp::Named((a, _), Some(args)) => {
            let mut args_iter = args.into_iter();
            match a.string.as_str() {
                "Option" => Some(CarrierTyp::Option(args_iter.next().unwrap())),
                "Result" => Some(CarrierTyp::Result(
                    args_iter.next().unwrap(),
                    args_iter.next().unwrap(),
                )),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Typechecks an expression, then elaborates
/// [`MonadicLet`][Expression::MonadicLet] nodes, and possibly extract
/// an [`EarlyReturnType`][EarlyReturnType].
fn typecheck_expression_qm(
    sess: &Session,
    e: &Spanned<Expression>,
    func_return_type: &Option<&Spanned<BaseTyp>>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
) -> TypecheckingResult<(Expression, Typ, Option<CarrierTyp>, VarContext)> {
    let (e, ty, vctx) =
        typecheck_expression(sess, e, func_return_type, top_level_context, var_context)?;
    let e = crate::elab_monadic_lets::eliminate_question_marks_in_expressions(&e);
    Ok((
        e.clone(),
        ty,
        match e {
            Expression::MonadicLet(carrier, ..) => Some(carrier),
            _ => None,
        },
        vctx,
    ))
}

/// Typechecks and elaborate an expression which is expected to
/// contain no question mark. In the case the expression is monadic
/// (i.e. contains a question mark), the function throws an error.
fn typecheck_expression_no_qm(
    sess: &Session,
    (e, e_span): &Spanned<Expression>,
    func_return_type: &Option<&Spanned<BaseTyp>>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
) -> TypecheckingResult<(Expression, Typ, VarContext)> {
    let e = &(e.clone(), e_span.clone());
    let (e, ty, carrier, vctx) =
        typecheck_expression_qm(sess, e, func_return_type, top_level_context, var_context)?;
    match carrier {
        Some(_) => Err(sess.span_rustspec_err(
            *e_span,
            format!("question mark cannot occur in this expression in Hacspec").as_str(),
        )),
        _ => Ok((e, ty, vctx)),
    }
}

/// TODO: rework `QuestionMarkInfo` in general. For now,
/// `QuestionMarkInfo` ships informations about question marks along
/// with mutation information. However, those two should be able to
/// live independently.
/// `merge_qmi_carrier` merges a `QuestionMarkInfo` with a `CarrierTyp`.
fn merge_qmi_carrier(
    qmi: &QuestionMarkInfo,
    carrier: &Option<CarrierTyp>,
    var_context: &VarContext, // Why are we discarding `qmi`'s `ScopeMutableVars`?
) -> QuestionMarkInfo {
    carrier
        .as_ref()
        .map(|carrier| {
            let mut_vars = translate_var_context_to_mut_vars(var_context.clone());
            let fun_deps = qmi.as_ref().map_or_else(
                || FunctionDependencies(HashSet::new()),
                |(_, fun_deps, _)| fun_deps.clone(),
            );
            (mut_vars, fun_deps, Some(dbg!(carrier).clone()))
        })
        .or_else(|| qmi.clone())
}

fn typecheck_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
    return_typ: &Spanned<BaseTyp>,
) -> TypecheckingResult<(Statement, Typ, VarContext, VarSet)> {
    log::trace!("typecheck_statement ({:?}, {:?})", s, s_span);
    match &s {
        Statement::LetBinding((pat, pat_span), typ, ref expr, question_mark) => {
            log::trace!("   Statement::LetBinding");
            log::trace!("       expr: {:?}", expr);
            #[cfg(feature = "dev")]
            log::trace!("   {:?}", backtrace::Backtrace::new());
            let (new_expr, expr_typ, carrier, new_var_context) = typecheck_expression_qm(
                sess,
                expr,
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            let expr_typ = typecheck_question_mark(
                sess,
                question_mark.clone().is_some(),
                expr_typ,
                return_typ,
                expr.1.clone(),
                top_level_context,
            )?;
            let typ = match typ {
                None => Some((expr_typ.clone(), expr.1.clone())),
                Some((inner_typ, _)) => {
                    if unify_types(
                        sess,
                        inner_typ,
                        &expr_typ,
                        &HashMap::new(),
                        top_level_context,
                    )?
                    .is_none()
                    {
                        sess.span_rustspec_err(
                            *pat_span,
                            format!(
                                "wrong type declared for variable: expected {}{}, found {}{}",
                                (inner_typ.0).0,
                                (inner_typ.1).0,
                                (expr_typ.0).0,
                                (expr_typ.1).0
                            )
                            .as_str(),
                        );
                        return Err(());
                    }

                    typ.clone()
                }
            };
            log::trace!("   typ: {:?}", typ);
            let pat_var_context = typecheck_pattern(
                sess,
                &(pat.clone(), pat_span.clone()),
                &expr_typ,
                top_level_context,
            )?;

            let mut ret_var_context = var_context
                .clone()
                .change(new_var_context.clone().union(pat_var_context));

            if let Pattern::IdentPat(x, true) = pat.clone() {
                match (x, typ.clone().map(|t| t.0)) {
                    (
                        Ident::Local(LocalIdent {
                            id,
                            name,
                            mutable: _,
                        }),
                        Some(var),
                    ) => {
                        // mutable should always be true
                        ret_var_context.mutable_vars =
                            ret_var_context.mutable_vars.update(id, (var, name, false))
                    }
                    _ => (),
                }
            };
            let question_mark = merge_qmi_carrier(question_mark, &carrier, &ret_var_context);
            Ok((
                Statement::LetBinding(
                    (pat.clone(), pat_span.clone()),
                    typ.clone(),
                    (new_expr, expr.1.clone()),
                    question_mark,
                ),
                ((Borrowing::Consumed, s_span), (UnitTyp, s_span)),
                ret_var_context,
                VarSet(HashSet::new()),
            ))
        }
        Statement::Reassignment((x, x_span), _x_typ, e, question_mark) => {
            log::trace!("   Statement::Reassignment");
            let (new_e, e_typ, carrier, new_var_context) = typecheck_expression_qm(
                sess,
                &e,
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            let e_typ = typecheck_question_mark(
                sess,
                question_mark.clone().is_some(),
                e_typ,
                return_typ,
                e.1.clone(),
                top_level_context,
            )?;
            let x_typ = find_typ(&x, var_context, top_level_context);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_rustspec_err(*x_span, "trying to reassign to an inexisting variable");
                    return Err(());
                }
            };
            if unify_types(sess, &e_typ, &x_typ, &HashMap::new(), top_level_context)?.is_none() {
                sess.span_rustspec_err(
                    e.1,
                    format!(
                        "variable {} has type {}{} but tried to reassign with an expression of type {}{}",
                        x, (x_typ.0).0, (x_typ.1).0, (e_typ.0).0, (e_typ.1).0
                    ).as_str(),
                );
                return Err(());
            };
            let ret_var_context = add_var(&x, &x_typ, &new_var_context);
            let question_mark = merge_qmi_carrier(question_mark, &carrier, &ret_var_context);
            Ok((
                Statement::Reassignment(
                    (x.clone(), x_span.clone()),
                    Some((x_typ.clone(), x_span.clone())),
                    (new_e, e.1.clone()),
                    question_mark,
                ),
                ((Borrowing::Consumed, s_span), (UnitTyp, s_span)),
                ret_var_context,
                VarSet(HashSet::unit(match x.clone() {
                    Ident::Local(x) => x,
                    _ => panic!("should not happen"),
                })),
            ))
        }
        Statement::ArrayUpdate((x, x_span), e1, e2, question_mark, _) => {
            log::trace!("   Statement::ArrayUpdate");
            let (new_e1, e1_t, carrier1, var_context) = typecheck_expression_qm(
                sess,
                &e1,
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            let (new_e2, e2_t, carrier2, var_context) = typecheck_expression_qm(
                sess,
                &e2,
                &Some(return_typ),
                top_level_context,
                &var_context,
            )?;
            let e2_t = typecheck_question_mark(
                sess,
                question_mark.clone().is_some(),
                e2_t,
                return_typ,
                e2.1.clone(),
                top_level_context,
            )?;
            if !is_index(&(e1_t.1).0, top_level_context) {
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
            let (_, cell_t) = is_array(sess, &x_typ, top_level_context, x_span)?;
            if unify_types(
                sess,
                &e2_t,
                &((Borrowing::Consumed, x_span.clone()), cell_t.clone()),
                &HashMap::new(),
                top_level_context,
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

            let question_mark = match (carrier1, carrier2) {
                (Some(c), _) | (_, Some(c)) => question_mark.clone().map(|(_, fun_dep, _)| {
                    (
                        translate_var_context_to_mut_vars(var_context.clone()),
                        fun_dep,
                        early_return_type_from_return_type(top_level_context, return_typ.clone().0), // Some(c),
                    )
                }),
                _ => None,
            };

            Ok((
                Statement::ArrayUpdate(
                    (x.clone(), x_span.clone()),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                    question_mark,
                    Some(x_typ),
                ),
                ((Borrowing::Consumed, s_span), (UnitTyp, s_span)),
                var_context,
                VarSet(HashSet::unit(match x.clone() {
                    Ident::Local(x) => x,
                    _ => panic!("should not happen"),
                })),
            ))
        }
        Statement::ReturnExp(e, _) => {
            log::trace!("   Statement::ReturnExp");
            let (new_e, e_t, _, var_context) = typecheck_expression_qm(
                sess,
                &(e.clone(), s_span),
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            Ok((
                Statement::ReturnExp(new_e, Some(e_t.clone())),
                e_t,
                var_context,
                VarSet(HashSet::new()),
            ))
        }
        Statement::Conditional(cond, (b1, b1_span), b2, _) => {
            log::trace!("   Statement::Conditional");
            let original_var_context = var_context;
            let (new_cond, cond_t, var_context) = typecheck_expression_no_qm(
                sess,
                &cond,
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            unify_types_default_error_message(
                sess,
                &cond_t,
                &(
                    (Borrowing::Consumed, (cond_t.0).1),
                    (BaseTyp::Bool, (cond_t.1).1),
                ),
                &HashMap::new(),
                top_level_context,
            )?;
            let (new_b1, var_context_b1) = typecheck_block(
                sess,
                (b1.clone(), b1_span.clone()),
                top_level_context,
                &var_context,
                return_typ,
            )?;
            let (new_b2, var_context_b2) = match b2 {
                None => (None, var_context.clone()),
                Some((b2, b2_span)) => {
                    let (new_b2, var_context_b2) = typecheck_block(
                        sess,
                        (b2.clone(), b2_span.clone()),
                        top_level_context,
                        &var_context,
                        return_typ,
                    )?;
                    (Some((new_b2, *b2_span)), var_context_b2)
                }
            };
            match &new_b1.return_typ {
                None => panic!("should not happen"),
                Some(((Borrowing::Consumed, _), (BaseTyp::Tuple(tup), _))) if tup.is_empty() => (),
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
                        None => panic!("should not happen"),
                        Some(((Borrowing::Consumed, _), (BaseTyp::Tuple(tup), _)))
                            if tup.is_empty() =>
                        {
                            ()
                        }
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
            let new_mutated = VarSet(
                match &new_b1.mutated {
                    None => HashSet::new(),
                    Some(m) => m.vars.0.clone(),
                }
                .union(match &new_b2 {
                    None => HashSet::new(),
                    Some((new_b2, _)) => match &new_b2.mutated {
                        None => HashSet::new(),
                        Some(m) => m.vars.0.clone(),
                    },
                }),
            );
            let mut_tuple = var_set_to_tuple(&new_mutated, &s_span, &var_context);
            let ret_var_context = original_var_context
                .clone()
                .intersection(var_context_b1)
                .intersection(var_context_b2);
            Ok((
                Statement::Conditional(
                    (new_cond, cond.1.clone()),
                    (new_b1, *b1_span),
                    new_b2,
                    Some(Box::new(MutatedInfo {
                        vars: new_mutated.clone(),
                        early_return_type: early_return_type_from_return_type(
                            top_level_context,
                            return_typ.0.clone(),
                        ),
                        stmt: mut_tuple,
                    })),
                ),
                ((Borrowing::Consumed, s_span), (UnitTyp, s_span)),
                ret_var_context,
                new_mutated,
            ))
        }
        Statement::ForLoop(x, e1, e2, (b, b_span)) => {
            log::trace!("   Statement::ForLoop");
            let original_var_context = var_context;
            let (new_e1, t_e1, var_context) = typecheck_expression_no_qm(
                sess,
                e1,
                &Some(return_typ),
                top_level_context,
                var_context,
            )?;
            let (new_e2, t_e2, var_context) = typecheck_expression_no_qm(
                sess,
                e2,
                &Some(return_typ),
                top_level_context,
                &var_context,
            )?;
            match (
                t_e1.0.clone(),
                dealias_type(t_e1.1 .0.clone(), top_level_context),
            ) {
                ((Borrowing::Consumed, _), BaseTyp::Usize) => (),
                _ => {
                    sess.span_rustspec_err(
                        e1.1,
                        format!(
                            "loop range bound should be an usize but has type {}{}",
                            (t_e1.0).0,
                            (t_e1.1).0
                        )
                        .as_str(),
                    );
                    return Err(());
                }
            };
            match (
                t_e2.0.clone(),
                dealias_type(t_e2.1 .0.clone(), top_level_context),
            ) {
                ((Borrowing::Consumed, _), BaseTyp::Usize) => (),
                _ => {
                    sess.span_rustspec_err(
                        e2.1,
                        format!(
                            "loop range bound should be an usize but has type {}{}",
                            (t_e2.0).0,
                            (t_e2.1).0
                        )
                        .as_str(),
                    );
                    return Err(());
                }
            };
            let var_context = match x {
                None => var_context,
                Some((x, x_span)) => add_var(
                    &x,
                    &((Borrowing::Consumed, *x_span), (BaseTyp::Usize, *x_span)),
                    &var_context,
                ),
            };
            let (new_b, var_context) = typecheck_block(
                sess,
                (b.clone(), b_span.clone()),
                top_level_context,
                &var_context,
                return_typ,
            )?;
            let mutated_vars = new_b.mutated.as_ref().unwrap().as_ref().vars.clone();
            // Linear variables cannot be consumed in the body of the loop, so we check that
            let var_diff = original_var_context
                .clone()
                .vars
                .difference(var_context.clone().vars);
            for (var_diff_id, (_, var_diff_name, _)) in var_diff {
                if original_var_context.vars.contains_key(&var_diff_id) {
                    sess.span_rustspec_err(
                        b_span.clone(),
                        format!("loop body consumes linear variable: {}", var_diff_name).as_str(),
                    );
                    return Err(());
                }
            }
            let ret_var_context = original_var_context.clone().intersection(var_context);
            Ok((
                Statement::ForLoop(
                    x.clone(),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                    (new_b, *b_span),
                ),
                ((Borrowing::Consumed, s_span), (UnitTyp, s_span)),
                ret_var_context,
                mutated_vars,
            ))
        }
    }
}

fn typecheck_block(
    sess: &Session,
    (b, b_span): Spanned<Block>,
    top_level_context: &TopLevelContext,
    original_var_context: &VarContext,
    function_return_typ: &Spanned<BaseTyp>,
) -> TypecheckingResult<(Block, VarContext)> {
    log::trace!("typecheck_block ({:?}, {:?})", b, b_span);
    let mut var_context = original_var_context.clone();
    let mut mutated_vars = VarSet(HashSet::new());
    let mut return_typ = Some((
        (Borrowing::Consumed, DUMMY_SP.into()),
        (UnitTyp, DUMMY_SP.into()),
    ));
    let mut new_stmts = Vec::new();
    let n_stmts = b.stmts.len();
    for (i, s) in b.stmts.into_iter().enumerate() {
        let s_span = s.1.clone();
        log::trace!("   s {:?}", s);
        let (new_stmt, stmt_typ, new_var_context, new_mutated_vars) = typecheck_statement(
            sess,
            s,
            top_level_context,
            &var_context,
            function_return_typ,
        )?;
        new_stmts.push((new_stmt, s_span));
        var_context = var_context.change(new_var_context.clone());
        mutated_vars = VarSet(mutated_vars.0.clone().union(new_mutated_vars.0));
        if i + 1 < n_stmts {
            // Statement return types should be unit except for the last one
            match stmt_typ {
                ((Borrowing::Consumed, _), (BaseTyp::Tuple(tup), _)) if tup.is_empty() => (),
                _ => {
                    sess.span_rustspec_err(s_span, "statement shoud have an unit type here");
                    return Err(());
                }
            }
        } else {
            return_typ = Some(stmt_typ)
        }
    }
    // We only keep in the list of mutated vars of this block the ones that
    // were defined at the beginning of the block
    mutated_vars
        .0
        .retain(|mut_var| original_var_context.vars.contains_key(&mut_var.id));
    let mut_tuple = var_set_to_tuple(&mutated_vars, &b_span, &var_context);
    let contains_question_mark = Some(new_stmts.iter().any(|s| match s {
        (Statement::Reassignment(_, _, _, Some(_)), _)
        | (Statement::LetBinding(_, _, _, Some(_)), _) => true,
        (Statement::Conditional(_, then_b, else_b, _), _) => {
            then_b.0.contains_question_mark.unwrap()
                || (match else_b {
                    None => false,
                    Some(else_b) => else_b.0.contains_question_mark.unwrap(),
                })
        }
        (Statement::ForLoop(_, _, _, loop_b), _) => loop_b.0.contains_question_mark.unwrap(),
        _ => false,
    }));
    let new_var_context = var_context.intersection(original_var_context.clone());

    Ok((
        Block {
            stmts: new_stmts,
            mutated: Some(Box::new(MutatedInfo {
                vars: mutated_vars,
                early_return_type: early_return_type_from_return_type(
                    top_level_context,
                    function_return_typ.0.clone(),
                ),
                stmt: mut_tuple,
            })),
            return_typ,
            contains_question_mark,
            mutable_vars: translate_var_context_to_mut_vars(new_var_context.clone()),
            function_dependencies: b.function_dependencies,
        },
        new_var_context,
    ))
}

fn typecheck_item(
    sess: &Session,
    item: &DecoratedItem,
    top_level_context: &mut TopLevelContext,
) -> TypecheckingResult<DecoratedItem> {
    log::trace!("typecheck_item ({:#?})", item);
    let i = &item.item;
    let i = match &i {
        Item::NaturalIntegerDecl(typ_ident, secrecy, canvas_size, info) => {
            let canvas_size_span = canvas_size.1.clone();
            let (new_canvas_size, canvas_size_typ, _) = typecheck_expression_no_qm(
                sess,
                canvas_size,
                &None,
                top_level_context,
                &VarContext::new(),
            )?;
            if let None = unify_types(
                sess,
                &(
                    (Borrowing::Consumed, canvas_size_span),
                    (BaseTyp::Usize, canvas_size_span),
                ),
                &canvas_size_typ,
                &HashMap::new(),
                top_level_context,
            )? {
                sess.span_rustspec_err(
                    canvas_size_span,
                    format!(
                        "expected type usize, got {}{}",
                        (canvas_size_typ.0).0,
                        (canvas_size_typ.1).0
                    )
                    .as_str(),
                )
            };
            Ok(Item::NaturalIntegerDecl(
                typ_ident.clone(),
                secrecy.clone(),
                (new_canvas_size, canvas_size_span),
                info.clone(),
            ))
        }
        Item::AliasDecl(_, _) | Item::ImportedCrate(_) | Item::EnumDecl(_, _) => Ok(i.clone()),
        Item::FnDecl((f, f_span), sig, (b, b_span)) => {
            log::trace!("   Item::FnDecl");
            let var_context = VarContext::new();
            let var_context = sig
                .args
                .iter()
                .fold(var_context, |var_context, ((x, _x_span), (t, _t_span))| {
                    add_var(&x, t, &var_context)
                });
            let (new_b, _final_var_context) = typecheck_block(
                sess,
                (b.clone(), b_span.clone()),
                top_level_context,
                &var_context,
                &sig.ret,
            )?;
            let comp_ret_typ = &new_b.return_typ.clone().unwrap();
            if let None = unify_types(
                sess,
                comp_ret_typ,
                &((Borrowing::Consumed, DUMMY_SP.into()), sig.ret.clone()),
                &HashMap::new(),
                top_level_context,
            )? {
                sess.span_rustspec_err(
                    sig.ret.1.clone(),
                    format!(
                        "expected type {}, got {}{}",
                        sig.ret.0,
                        (comp_ret_typ.0).0,
                        (comp_ret_typ.1).0,
                    )
                    .as_str(),
                )
            }
            let mut new_sig = sig.clone();
            new_sig.mutable_vars = new_b.clone().mutable_vars;
            top_level_context.functions.insert(
                FnKey::Independent(f.clone()),
                FnValue::Local(new_sig.clone()),
            );
            let out = Item::FnDecl(
                (f.clone(), f_span.clone()),
                new_sig.clone(),
                (new_b, b_span.clone()),
            );
            Ok(out)
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let (new_size, size_typ, _) = typecheck_expression_no_qm(
                sess,
                size,
                &None,
                top_level_context,
                &VarContext::new(),
            )?;
            if let None = unify_types(
                sess,
                &(
                    (Borrowing::Consumed, size.1.clone()),
                    (BaseTyp::Usize, size.1.clone()),
                ),
                &size_typ,
                &HashMap::new(),
                top_level_context,
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
            Ok(Item::ArrayDecl(
                id.clone(),
                (new_size, size.1.clone()),
                cell_t.clone(),
                index_typ.clone(),
            ))
        }
        Item::ConstDecl(id, typ, e) => {
            let (new_e, new_t, _) =
                typecheck_expression_no_qm(sess, e, &None, top_level_context, &VarContext::new())?;
            if let None = unify_types(
                sess,
                &((Borrowing::Consumed, typ.1.clone()), typ.clone()),
                &new_t,
                &HashMap::new(),
                top_level_context,
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
            Ok(Item::ConstDecl(
                id.clone(),
                typ.clone(),
                (new_e, (e.1).clone()),
            ))
        }
    };
    match i {
        Ok(i) => Ok(DecoratedItem {
            item: i,
            tags: item.tags.clone(),
        }),
        Err(a) => Err(a),
    }
}

pub fn typecheck_program(
    sess: &Session,
    p: &Program,
    top_level_ctx: &mut TopLevelContext,
) -> TypecheckingResult<Program> {
    Ok(Program {
        items: check_vec(
            p.items
                .iter()
                .map(|(i, i_span)| {
                    let new_i = typecheck_item(sess, i, top_level_ctx)?;
                    Ok((new_i, i_span.clone()))
                })
                .collect(),
        )?,
    })
}
