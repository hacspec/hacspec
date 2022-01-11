use crate::name_resolution::{DictEntry, FnKey, FnValue, TopLevelContext};
use crate::rustspec::*;
use crate::util::check_vec;
use crate::HacspecErrorEmitter;

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

type VarContext = HashMap<usize, (Typ, String)>;

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
    match x {
        Ident::Unresolved(_) => panic!("name resolution should have already happened"),
        Ident::TopLevel(name) => top_level_context.consts.get(name).map(|(t, span)| {
            (
                (Borrowing::Consumed, span.clone()),
                (t.clone(), span.clone()),
            )
        }),
        Ident::Local(LocalIdent { name: _, id }) => var_context.get(id).map(|x| x.0.clone()),
    }
}

fn remove_var(x: &Ident, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Local(LocalIdent { id, name: _ }) => var_context.without(id),
        _ => panic!("trying to lookup in the var context a non-local id"),
    }
}

fn add_var(x: &Ident, typ: &Typ, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Local(LocalIdent { id, name }) => {
            var_context.update(id.clone(), (typ.clone(), name.clone()))
        }
        _ => panic!("trying to lookup in the var context a non-local id"),
    }
}

pub type TypecheckingResult<T> = Result<T, ()>;

fn typecheck_expression(
    sess: &Session,
    (e, span): &Spanned<Expression>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
) -> TypecheckingResult<(Expression, Typ, VarContext)> {
    match e {
        Expression::Tuple(args) => {
            let mut var_context = var_context.clone();
            let new_and_typ_args = args
                .iter()
                .map(|arg| {
                    let (new_arg, ((arg_typ_borrowing, _), arg_typ), new_var_context) =
                        typecheck_expression(sess, arg, top_level_context, &var_context)?;
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
                        if is_copy(&(t.1).0, top_level_context) {
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
        Expression::MatchWith(arg, arms) => {
            let (new_arg, t_arg, intermediate_var_context) =
                typecheck_expression(sess, arg, top_level_context, &var_context)?;
            let mut acc_var_context = intermediate_var_context.clone();
            // First we retrieve the enum type that's being matched on as well
            // as diverse infos related to it
            let (mut t_arg_cases, t_arg_enum_name, t_arg_enum_args, enum_type_var_args) =
                match (t_arg.1).0.clone() {
                    BaseTyp::Named((name, _), args) => {
                        match top_level_context.typ_dict.get(&name) {
                            Some((
                                (
                                    (Borrowing::Consumed, _),
                                    (BaseTyp::Enum(cases, type_args_vars), _),
                                ),
                                DictEntry::Enum,
                            )) => (
                                cases.clone(),
                                name.clone(),
                                args.clone(),
                                type_args_vars.clone(),
                            ),
                            _ => {
                                sess.span_rustspec_err(
                                    arg.1.clone(),
                                    format!(
                                        "expected an enum type, got {}{}",
                                        (t_arg.0).0,
                                        (t_arg.1).0
                                    )
                                    .as_str(),
                                );
                                return Err(());
                            }
                        }
                    }
                    _ => {
                        sess.span_rustspec_err(
                            arg.1.clone(),
                            format!("expected an enum type, got {}{}", (t_arg.0).0, (t_arg.1).0)
                                .as_str(),
                        );
                        return Err(());
                    }
                };
            let mut out_typ = None;
            // Then we typecheck each match arm
            let new_arms = check_vec(
                arms.into_iter()
                    .map(|(arm_enum_ty, arm_case, arm_pattern, arm_exp)| {
                        let arm_enum_ty = dealias_type(arm_enum_ty.clone(), top_level_context);
                        // The enum name is repeated in each match arm so we
                        // make sure it's the good one
                        let (arm_enum_name, arm_enum_args) = match &arm_enum_ty {
                            BaseTyp::Named((t_arm_ty_name, _), t_arm_ty_args) => {
                                if &t_arg_enum_name != t_arm_ty_name {
                                    sess.span_rustspec_err(
                                        arm_case.1.clone(),
                                        format!(
                                            "expected {} type, got {}",
                                            t_arg_enum_name, arm_enum_ty
                                        )
                                        .as_str(),
                                    );
                                    return Err(());
                                }
                                match top_level_context.typ_dict.get(&t_arm_ty_name) {
                                    Some((_, DictEntry::Enum)) => {
                                        (t_arm_ty_name.clone(), t_arm_ty_args.clone())
                                    }
                                    _ => {
                                        sess.span_rustspec_err(
                                            arm_case.1.clone(),
                                            format!("expected an enum type, got {}", arm_enum_ty)
                                                .as_str(),
                                        );
                                        return Err(());
                                    }
                                }
                            }
                            _ => {
                                sess.span_rustspec_err(
                                    arm_case.1.clone(),
                                    format!("expected an enum type, got {}", arm_enum_ty).as_str(),
                                );
                                return Err(());
                            }
                        };
                        // Then we proceed with the typechecking, first
                        // by checking correctness of the enum generic
                        // arguments between those in the match arm and those
                        // coming from the expression being matched
                        let mut typ_var_ctx = HashMap::new();
                        match (&t_arg_enum_args, &arm_enum_args) {
                            (None, None) => (),
                            (Some(arg_args), Some(arms_args)) => {
                                if arg_args.len() != arms_args.len() {
                                    sess.span_rustspec_err(
                                        arm_case.1.clone(),
                                        "discrepancy between the type arguments \
                                        of the matched expression and those of the match arm",
                                    );
                                    return Err(());
                                }
                                for ((arg_arg, arm_arg), enum_type_var_arg) in arg_args
                                    .iter()
                                    .zip(arms_args)
                                    .zip(enum_type_var_args.iter())
                                {
                                    unify_types_default_error_message(
                                        sess,
                                        &((Borrowing::Consumed, DUMMY_SP.into()), arg_arg.clone()),
                                        &((Borrowing::Consumed, DUMMY_SP.into()), arm_arg.clone()),
                                        &HashMap::new(),
                                        top_level_context,
                                    )?;
                                    let new_typ_var_ctx = unify_types(
                                        sess,
                                        &((Borrowing::Consumed, DUMMY_SP.into()), arg_arg.clone()),
                                        &(
                                            (Borrowing::Consumed, DUMMY_SP.into()),
                                            (
                                                BaseTyp::Variable(enum_type_var_arg.clone()),
                                                DUMMY_SP.into(),
                                            ),
                                        ),
                                        &HashMap::new(),
                                        top_level_context,
                                    )?;
                                    match new_typ_var_ctx {
                                        Some(new_typ_var_ctx) => {
                                            typ_var_ctx = typ_var_ctx.union(new_typ_var_ctx);
                                        }
                                        None => {
                                            sess.span_rustspec_err(
                                                arm_arg.1.clone(),
                                                format!(
                                                    "expected {} type, got {}",
                                                    arg_arg.0, arm_arg.0
                                                )
                                                .as_str(),
                                            );
                                            return Err(());
                                        }
                                    }
                                }
                            }
                            _ => {
                                sess.span_rustspec_err(
                                    arm_case.1.clone(),
                                    "discrepancy between the type arguments \
                                    of the matched expression and those of the match arm",
                                );
                                return Err(());
                            }
                        };
                        // Then we finally proceed with typechecking the arm
                        // expression, for that we retrieve the type of this arm's
                        // payload
                        let (case_index, case_typ) =
                            match t_arg_cases.iter().enumerate().find(
                                |(_, ((t_arg_case_name, _), _))| &arm_case.0 == t_arg_case_name,
                            ) {
                                Some((case_index, (_, t_arg_case_typ))) => {
                                    (case_index, t_arg_case_typ.clone())
                                }
                                None => {
                                    sess.span_rustspec_err(
                                        arm_case.1.clone(),
                                        format!("enum case not found for {}", arm_enum_name.string)
                                            .as_str(),
                                    );
                                    return Err(());
                                }
                            };
                        let case_typ = match case_typ {
                            Some(case_typ) => Some((
                                bind_variable_type(sess, &case_typ, &typ_var_ctx)?,
                                case_typ.1.clone(),
                            )),
                            None => None,
                        };
                        t_arg_cases.remove(case_index);
                        // t_arg_cases stores the arms not covered by the match
                        // yet
                        let (new_arm_pattern, new_var_context) = match (arm_pattern, case_typ) {
                            (None, None) => (None, HashMap::new()),
                            (Some(arm_pattern), Some(case_typ)) => {
                                let new_var_context = typecheck_pattern(
                                    sess,
                                    arm_pattern,
                                    &(t_arg.0.clone(), case_typ.clone()),
                                    top_level_context,
                                )?;
                                (Some(arm_pattern.clone()), new_var_context)
                            }
                            _ => {
                                sess.span_rustspec_err(
                                    arm_case.1.clone(),
                                    format!("pattern not coherent with expected type").as_str(),
                                );
                                return Err(());
                            }
                        };
                        let (new_arm_exp, arm_typ, new_var_context) = typecheck_expression(
                            sess,
                            arm_exp,
                            top_level_context,
                            &intermediate_var_context.clone().union(new_var_context),
                        )?;
                        acc_var_context = acc_var_context.clone().intersection(new_var_context);
                        match &out_typ {
                            None => out_typ = Some(arm_typ),
                            Some(out_typ) => {
                                unify_types_default_error_message(
                                    sess,
                                    &arm_typ,
                                    out_typ,
                                    &HashMap::new(),
                                    top_level_context,
                                )?;
                            }
                        };
                        Ok((
                            arm_enum_ty.clone(),
                            arm_case.clone(),
                            new_arm_pattern,
                            (new_arm_exp, arm_exp.1.clone()),
                        ))
                    })
                    .collect(),
            )?;
            // Finally, we check whether all match arms have been included
            if t_arg_cases.len() > 0 {
                sess.span_rustspec_err(
                    span.clone(),
                    format!(
                        "some cases are missing in the match: {}",
                        t_arg_cases
                            .into_iter()
                            .map(|((t_case, _), _)| format!("{}", t_case))
                            .format(", ")
                    )
                    .as_str(),
                );
                return Err(());
            }
            Ok((
                Expression::MatchWith(Box::new((new_arg, arg.1.clone())), new_arms),
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
            let (new_cond, t_cond, var_context) =
                typecheck_expression(sess, cond, top_level_context, &var_context)?;
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
                typecheck_expression(sess, e_t, top_level_context, &var_context)?;
            let (new_e_f, t_e_f, var_context_false_branch) =
                typecheck_expression(sess, e_f, top_level_context, &var_context)?;
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
                typecheck_expression(sess, e1, top_level_context, var_context)?;
            let (new_e2, t2, var_context) =
                typecheck_expression(sess, e2, top_level_context, &var_context)?;
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
                typecheck_expression(sess, e1, top_level_context, var_context)?;
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
                typecheck_expression(sess, e2, top_level_context, &var_context)?;
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
        Expression::FuncCall(prefix, name, args) => {
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
            for (sig_t, ((arg, arg_span), (arg_borrow, arg_borrow_span))) in
                sig_args.iter().zip(args)
            {
                let (new_arg, arg_t, new_var_context) = typecheck_expression(
                    sess,
                    &(arg.clone(), arg_span.clone()),
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
            let (_, sel_typ, _) =
                typecheck_expression(sess, &sel, top_level_context, &var_context)?;
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
        Expression::IntegerCasting(e1, t1, _) => {
            let (new_e1, e1_typ, var_context) =
                typecheck_expression(sess, e1, top_level_context, var_context)?;
            if (e1_typ.0).0 == Borrowing::Borrowed {
                sess.span_rustspec_err(e1.1.clone(), "cannot cast borrowed expression");
                return Err(());
            }
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
            Ok((
                Expression::IntegerCasting(
                    Box::new((new_e1, e1.1.clone())),
                    t1.clone(),
                    Some((e1_typ.1).0.clone()),
                ),
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
            Pattern::SingleCaseEnum((pat_enum_name, _), inner_pat),
            BaseTyp::Named((typ_name, _), None),
        ) if pat_enum_name == typ_name => match top_ctx.typ_dict.get(typ_name) {
            Some((
                ((Borrowing::Consumed, _), (BaseTyp::Enum(cases, _type_args), cases_span)),
                DictEntry::Enum,
            )) => {
                if cases.len() != 1 {
                    sess.span_rustspec_err(
                        *pat_span,
                        format!(
                            "this pattern is matching the enum {} with multiple cases",
                            pat_enum_name
                        )
                        .as_str(),
                    );
                    return Err(());
                }
                let ((case_name, _), case_typ) = cases.into_iter().next().unwrap();
                if case_name.string != pat_enum_name.string {
                    sess.span_rustspec_err(
                        *pat_span,
                        format!(
                            "this pattern matches the enum {} with a single case instead of the wrapper struct {}",
                            case_name,
                            pat_enum_name,
                        )
                        .as_str(),
                    );
                    return Err(());
                }
                match case_typ {
                    None => {
                        sess.span_rustspec_err(
                            *pat_span,
                            format!(
                                "this pattern is matching the enum {} with one case but no payload",
                                pat_enum_name
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                    Some((case_typ, _)) => typecheck_pattern(
                        sess,
                        inner_pat,
                        &(
                            borrowing_typ.clone(), // This propagates the borrowing down the enum
                            (case_typ.clone(), cases_span.clone()),
                        ),
                        top_ctx,
                    ),
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
        (Pattern::SingleCaseEnum(name, _), _) => {
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
                Ok(HashMap::new()),
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
        (Pattern::WildCard, _) => Ok(HashMap::new()),
        (Pattern::IdentPat(x), _) => {
            let (id, name) = match &x {
                Ident::Local(LocalIdent { id, name }) => (id.clone(), name.clone()),
                _ => panic!("should not happen"),
            };
            Ok(HashMap::unit(
                id,
                ((borrowing_typ.clone(), typ.clone()), name),
            ))
        }
    }
}

fn var_set_to_tuple(vars: &VarSet, span: &RustspecSpan) -> Statement {
    Statement::ReturnExp(if vars.0.len() > 0 {
        Expression::Tuple(
            vars.0
                .iter()
                .sorted()
                .map(|i| (Expression::Named(Ident::Local(i.clone())), span.clone()))
                .collect(),
        )
    } else {
        Expression::Lit(Literal::Unit)
    })
}

fn dealias_type(ty: BaseTyp, top_level_context: &TopLevelContext) -> BaseTyp {
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
    let mut expr_typ = (
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
        match expr_typ {
            (
                (Borrowing::Consumed, _),
                (BaseTyp::Named((TopLevelIdent { string: name, .. }, _), Some(args)), _),
            ) if name == "Option" && args.len() == 1 => {
                let some_typ = &args[0];
                match return_typ {
                    (
                        BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: return_name,
                                    ..
                                },
                                _,
                            ),
                            Some(return_args),
                        ),
                        _,
                    ) if return_name == "Option" && return_args.len() == 1 => {
                        expr_typ = ((Borrowing::Consumed, some_typ.1.clone()), some_typ.clone());
                    }
                    _ => {
                        sess.span_rustspec_err(
                            return_typ.1,
                            format!(
                                "expected a option type for this \
                    return type because of a question mark in the function, got {}",
                                return_typ.0,
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                }
            }
            (
                (Borrowing::Consumed, _),
                (BaseTyp::Named((TopLevelIdent { string: name, .. }, _), Some(args)), _),
            ) if name == "Result" && args.len() == 2 => {
                let ok_typ = &args[0];
                let err_typ = &args[1];
                match return_typ {
                    (
                        BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: return_name,
                                    ..
                                },
                                _,
                            ),
                            Some(return_args),
                        ),
                        _,
                    ) if return_name == "Result" && return_args.len() == 2 => {
                        let err_typ_ret = &args[1];
                        match unify_types(
                            sess,
                            &((Borrowing::Consumed, err_typ.1.clone()), err_typ.clone()),
                            &(
                                (Borrowing::Consumed, err_typ_ret.1.clone()),
                                err_typ_ret.clone(),
                            ),
                            &HashMap::new(),
                            top_level_context,
                        )? {
                            Some(_) => {
                                expr_typ =
                                    ((Borrowing::Consumed, ok_typ.1.clone()), ok_typ.clone());
                            }
                            None => {
                                sess.span_rustspec_err(
                                    expr_span,
                                    format!(
                                        "the type returned in case of error by this \
                                        expression is {}, expected {}",
                                        err_typ.0, err_typ_ret.0,
                                    )
                                    .as_str(),
                                );
                                return Err(());
                            }
                        }
                    }
                    _ => {
                        sess.span_rustspec_err(
                            return_typ.1,
                            format!(
                                "expected a result type for this \
                    return type because of a question mark in the function, got {}",
                                return_typ.0,
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                }
            }
            _ => {
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
                return Err(());
            }
        }
    }
    Ok(expr_typ)
}

fn early_return_type_from_return_type(
    top_level_context: &TopLevelContext,
    return_typ: BaseTyp,
) -> Fillable<EarlyReturnType> {
    match dealias_type(return_typ, top_level_context) {
        BaseTyp::Named((a, _), _) => match a.string.as_str() {
            "Option" => Some(EarlyReturnType::Option),
            "Result" => Some(EarlyReturnType::Result),
            _ => None,
        },
        _ => None,
    }
}

fn typecheck_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    top_level_context: &TopLevelContext,
    var_context: &VarContext,
    return_typ: &Spanned<BaseTyp>,
) -> TypecheckingResult<(Statement, Typ, VarContext, VarSet)> {
    match &s {
        Statement::LetBinding((pat, pat_span), typ, ref expr, question_mark) => {
            let (new_expr, expr_typ, new_var_context) =
                typecheck_expression(sess, expr, top_level_context, var_context)?;
            let expr_typ = typecheck_question_mark(
                sess,
                *question_mark,
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
            let pat_var_context = typecheck_pattern(
                sess,
                &(pat.clone(), pat_span.clone()),
                &expr_typ,
                top_level_context,
            )?;
            Ok((
                Statement::LetBinding(
                    (pat.clone(), pat_span.clone()),
                    typ.clone(),
                    (new_expr, expr.1.clone()),
                    *question_mark,
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                new_var_context.clone().union(pat_var_context),
                VarSet(HashSet::new()),
            ))
        }
        Statement::Reassignment((x, x_span), e, question_mark) => {
            let (new_e, e_typ, new_var_context) =
                typecheck_expression(sess, &e, top_level_context, var_context)?;
            let e_typ = typecheck_question_mark(
                sess,
                *question_mark,
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
            Ok((
                Statement::Reassignment(
                    (x.clone(), x_span.clone()),
                    (new_e, e.1.clone()),
                    *question_mark,
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                add_var(&x, &x_typ, &new_var_context),
                VarSet(HashSet::unit(match x.clone() {
                    Ident::Local(x) => x,
                    _ => panic!("should not happen"),
                })),
            ))
        }
        Statement::ArrayUpdate((x, x_span), e1, e2, question_mark, _) => {
            let (new_e1, e1_t, var_context) =
                typecheck_expression(sess, &e1, top_level_context, var_context)?;
            let (new_e2, e2_t, var_context) =
                typecheck_expression(sess, &e2, top_level_context, &var_context)?;
            let e2_t = typecheck_question_mark(
                sess,
                *question_mark,
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
            Ok((
                Statement::ArrayUpdate(
                    (x.clone(), x_span.clone()),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                    *question_mark,
                    Some(x_typ),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                var_context,
                VarSet(HashSet::unit(match x.clone() {
                    Ident::Local(x) => x,
                    _ => panic!("should not happen"),
                })),
            ))
        }
        Statement::ReturnExp(e) => {
            let (new_e, e_t, var_context) =
                typecheck_expression(sess, &(e.clone(), s_span), top_level_context, var_context)?;
            Ok((
                Statement::ReturnExp(new_e),
                e_t,
                var_context,
                VarSet(HashSet::new()),
            ))
        }
        Statement::Conditional(cond, (b1, b1_span), b2, _) => {
            let original_var_context = var_context;
            let (new_cond, cond_t, var_context) =
                typecheck_expression(sess, &cond, top_level_context, var_context)?;
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
                        None => panic!("should not happen"),
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
            let mut_tuple = var_set_to_tuple(&new_mutated, &s_span);
            Ok((
                Statement::Conditional(
                    (new_cond, cond.1.clone()),
                    (new_b1, *b1_span),
                    new_b2,
                    Some(Box::new(MutatedInfo {
                        vars: new_mutated.clone(),
                        early_return_type: early_return_type_from_return_type(top_level_context, return_typ.0.clone()),

                        stmt: mut_tuple,
                    })),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                original_var_context
                    .clone()
                    .intersection(var_context_b1)
                    .intersection(var_context_b2),
                new_mutated,
            ))
        }
        Statement::ForLoop(x, e1, e2, (b, b_span)) => {
            let original_var_context = var_context;
            let (new_e1, t_e1, var_context) =
                typecheck_expression(sess, e1, top_level_context, var_context)?;
            let (new_e2, t_e2, var_context) =
                typecheck_expression(sess, e2, top_level_context, &var_context)?;
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
                    x.clone(),
                    (new_e1, e1.1.clone()),
                    (new_e2, e2.1.clone()),
                    (new_b, *b_span),
                ),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                original_var_context.clone().intersection(var_context),
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
    let mut var_context = original_var_context.clone();
    let mut mutated_vars = VarSet(HashSet::new());
    let mut return_typ = Some((
        (Borrowing::Consumed, DUMMY_SP.into()),
        (BaseTyp::Unit, DUMMY_SP.into()),
    ));
    let mut new_stmts = Vec::new();
    let n_stmts = b.stmts.len();
    for (i, s) in b.stmts.into_iter().enumerate() {
        let s_span = s.1.clone();
        let (new_stmt, stmt_typ, new_var_context, new_mutated_vars) = typecheck_statement(
            sess,
            s,
            top_level_context,
            &var_context,
            function_return_typ,
        )?;
        new_stmts.push((new_stmt, s_span));
        var_context = new_var_context;
        mutated_vars = VarSet(mutated_vars.0.clone().union(new_mutated_vars.0));
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
    // We only keep in the list of mutated vars of this block the ones that
    // were defined at the beginning of the block
    mutated_vars
        .0
        .retain(|mut_var| original_var_context.contains_key(&mut_var.id));
    let mut_tuple = var_set_to_tuple(&mutated_vars, &b_span);
    let contains_question_mark = Some(new_stmts.iter().any(|s| match s {
        (Statement::Reassignment(_, _, true), _) | (Statement::LetBinding(_, _, _, true), _) => {
            true
        }
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

    Ok((
        Block {
            stmts: new_stmts,
            mutated: Some(Box::new(MutatedInfo {
                vars: mutated_vars,
                early_return_type: early_return_type_from_return_type(top_level_context, function_return_typ.0.clone()),
                stmt: mut_tuple,
            })),
            return_typ,
            contains_question_mark,
        },
        var_context.intersection(original_var_context.clone()),
    ))
}

fn typecheck_item(
    sess: &Session,
    item: &DecoratedItem,
    top_level_context: &TopLevelContext,
) -> TypecheckingResult<DecoratedItem> {
    let i = &item.item;
    let i = match &i {
        Item::NaturalIntegerDecl(typ_ident, secrecy, canvas_size, info) => {
            let canvas_size_span = canvas_size.1.clone();
            let (new_canvas_size, canvas_size_typ, _) =
                typecheck_expression(sess, canvas_size, top_level_context, &HashMap::new())?;
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
            let var_context = HashMap::new();
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
            let out = Item::FnDecl(
                (f.clone(), f_span.clone()),
                sig.clone(),
                (new_b, b_span.clone()),
            );
            Ok(out)
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let (new_size, size_typ, _) =
                typecheck_expression(sess, size, top_level_context, &HashMap::new())?;
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
                typecheck_expression(sess, e, top_level_context, &HashMap::new())?;
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
                    let new_i = typecheck_item(sess, i, &top_level_ctx)?;
                    Ok((new_i, i_span.clone()))
                })
                .collect(),
        )?,
    })
}
