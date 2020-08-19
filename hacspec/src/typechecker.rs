use crate::rustspec::*;
use hacspec_sig;
use im::{HashMap, HashSet};
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;
use rustc_span::Span;
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

// TODO: explain that we need typechecking inference to disambiguate method calls

pub static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_ident(x: &Ident) -> Ident {
    match x {
        Ident::Rustspec(_, _) => panic!("fresh_ident only replaces original Rust ident ids"),
        Ident::Original(n) => Ident::Rustspec(
            RustspecId(ID_COUNTER.fetch_add(1, Ordering::SeqCst)),
            n.clone(),
        ),
    }
}

fn is_numeric(t: &Typ) -> bool {
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
        _ => false,
    }
}

fn is_copy(t: &BaseTyp) -> bool {
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
        BaseTyp::Array(_, _) => true,
        // TODO: implement special cases for derived copy
        BaseTyp::Named(_, _) => false,
        BaseTyp::Variable(_) => false,
        BaseTyp::Tuple(ts) => ts.iter().all(|(t, _)| is_copy(t)),
    }
}

fn is_array(sess: &Session, t: &Typ, typ_dict: &TypeDict) -> Result<Spanned<BaseTyp>, ()> {
    match &(t.1).0 {
        BaseTyp::Seq(t1) => Ok(t1.as_ref().clone()),
        BaseTyp::Named(id, None) => match &id.0 {
            Ident::Rustspec(_, _) => panic!(),
            Ident::Original(name) => match typ_dict.get(name) {
                Some(new_t) => is_array(sess, new_t, typ_dict),
                None => {
                    sess.span_err(id.1.clone(), "unknown type");
                    Err(())
                }
            },
        },
        BaseTyp::Named(_, Some(_)) => Err(()),
        BaseTyp::Array(_, cell_t) => Ok(cell_t.as_ref().clone()),
        _ => Err(()),
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

type TypeVarCtx = HashMap<RustspecId, BaseTyp>;

fn unify_types(t1: &Typ, t2: &Typ, typ_ctx: &TypeVarCtx) -> Option<TypeVarCtx> {
    match (&(t1.0).0, &(t2.0).0) {
        (Borrowing::Consumed, Borrowing::Consumed) | (Borrowing::Borrowed, Borrowing::Borrowed) => {
            match (&(t1.1).0, &(t2.1).0) {
                (BaseTyp::Unit, BaseTyp::Unit) => Some(typ_ctx.clone()),
                (BaseTyp::Bool, BaseTyp::Bool) => Some(typ_ctx.clone()),
                (BaseTyp::UInt128, BaseTyp::UInt128) => Some(typ_ctx.clone()),
                (BaseTyp::Int128, BaseTyp::Int128) => Some(typ_ctx.clone()),
                (BaseTyp::UInt64, BaseTyp::UInt64) => Some(typ_ctx.clone()),
                (BaseTyp::Int64, BaseTyp::Int64) => Some(typ_ctx.clone()),
                (BaseTyp::UInt32, BaseTyp::UInt32) => Some(typ_ctx.clone()),
                (BaseTyp::Int32, BaseTyp::Int32) => Some(typ_ctx.clone()),
                (BaseTyp::UInt16, BaseTyp::UInt16) => Some(typ_ctx.clone()),
                (BaseTyp::Int16, BaseTyp::Int16) => Some(typ_ctx.clone()),
                (BaseTyp::UInt8, BaseTyp::UInt8) => Some(typ_ctx.clone()),
                (BaseTyp::Int8, BaseTyp::Int8) => Some(typ_ctx.clone()),
                (BaseTyp::Usize, BaseTyp::Usize) => Some(typ_ctx.clone()),
                (BaseTyp::Isize, BaseTyp::Isize) => Some(typ_ctx.clone()),
                (BaseTyp::Seq(tc1), BaseTyp::Seq(tc2)) => unify_types(
                    &(((Borrowing::Consumed, (t1.1).1)), *tc1.clone()),
                    &(((Borrowing::Consumed, (t2.1).1)), *tc2.clone()),
                    typ_ctx,
                ),
                (BaseTyp::Named(name1, arg1), BaseTyp::Named(name2, arg2)) => {
                    if match (&name1.0, &name2.0) {
                        (Ident::Original(name1), Ident::Original(name2)) => name1 == name2,
                        _ => panic!(), //should not happen
                    } {
                        match (&arg1, &arg2) {
                            (None, None) => None,
                            (Some(tc1), Some(tc2)) => unify_types(
                                &(((Borrowing::Consumed, (t1.1).1)), tc1.as_ref().clone()),
                                &(((Borrowing::Consumed, (t2.1).1)), tc2.as_ref().clone()),
                                typ_ctx,
                            ),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                (BaseTyp::Tuple(ts1), BaseTyp::Tuple(ts2)) => {
                    if ts1.len() == ts2.len() {
                        ts1.iter().zip(ts2.iter()).fold(
                            Some(typ_ctx.clone()),
                            |typ_ctx, (tc1, tc2)| {
                                typ_ctx.map_or(None, |typ_ctx| {
                                    unify_types(
                                        &(((Borrowing::Consumed, (t1.1).1)), tc1.clone()),
                                        &(((Borrowing::Consumed, (t2.1).1)), tc2.clone()),
                                        &typ_ctx,
                                    )
                                })
                            },
                        )
                    } else {
                        None
                    }
                }
                (BaseTyp::Variable(_), BaseTyp::Variable(_)) => None,
                (BaseTyp::Variable(id1), bt2) => Some(typ_ctx.update(id1.clone(), bt2.clone())),
                (bt1, BaseTyp::Variable(id2)) => Some(typ_ctx.update(id2.clone(), bt1.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}

fn bind_variable_type(ty: &BaseTyp, typ_ctx: &TypeVarCtx) -> BaseTyp {
    match &ty {
        BaseTyp::Variable(id) => match typ_ctx.get(&id) {
            None => panic!("type {} cannot be unified, internal Rustspec error", ty),
            Some(new_ty) => new_ty.clone(),
        },
        BaseTyp::Seq(arg_ty) => BaseTyp::Seq(Box::new((
            bind_variable_type(&arg_ty.as_ref().0, typ_ctx),
            arg_ty.as_ref().1.clone(),
        ))),
        BaseTyp::Named(name, arg) => BaseTyp::Named(
            name.clone(),
            arg.as_ref().map(|arg| {
                Box::new((
                    bind_variable_type(&arg.as_ref().0, typ_ctx),
                    arg.as_ref().1.clone(),
                ))
            }),
        ),
        BaseTyp::Tuple(args) => BaseTyp::Tuple(
            args.iter()
                .map(|(arg, span)| (bind_variable_type(arg, typ_ctx), span.clone()))
                .collect(),
        ),
        _ => ty.clone(),
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
    ExternalNotInRustspec,
}

fn sig_args(sig: &FnValue) -> Vec<Typ> {
    match sig {
        FnValue::Local(sig) => sig.args.clone().into_iter().map(|(_, (x, _))| x).collect(),
        FnValue::External(sig) => sig.args.clone(),
        FnValue::ExternalNotInRustspec => panic!(),
    }
}

fn sig_ret(sig: &FnValue) -> BaseTyp {
    match sig {
        FnValue::Local(sig) => sig.ret.0.clone(),
        FnValue::External(sig) => sig.ret.clone(),
        FnValue::ExternalNotInRustspec => panic!(),
    }
}

type FnContext = HashMap<FnKey, FnValue>;

type VarContext = HashMap<RustspecId, (Typ, String)>;

type TypeDict = HashMap<String, Typ>;

type NameContext = HashMap<String, Ident>;

type AllowedSigs = std::collections::HashSet<hacspec_sig::Signature>;

fn find_func(
    sess: &Session,
    key1: &FnKey,
    fn_context: &FnContext,
    span: &Span,
) -> TypecheckingResult<(FnValue, TypeVarCtx)> {
    let candidates = fn_context.clone();
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
                match unify_types(
                    &(
                        (Borrowing::Consumed, span.clone()),
                        (t1.clone(), span.clone()),
                    ),
                    &(
                        (Borrowing::Consumed, span.clone()),
                        (t2.clone(), span.clone()),
                    ),
                    &HashMap::new(),
                ) {
                    Some(new_typ_ctx) => match (n1, n2) {
                        (Ident::Original(n1), Ident::Original(n2)) => {
                            if n1 == n2 {
                                Some((new_typ_ctx, sig))
                            } else {
                                None
                            }
                        }
                        _ => panic!(),
                    },
                    None => None,
                }
            }
            _ => None,
        })
        .collect();
    if candidates.len() == 0 {
        sess.span_err(*span, format!("function {} cannot be found", key1).as_str());
        return Err(());
    }
    // If there are multiple candidates we just take the first one
    for (typ_ctx, sig) in candidates {
        return Ok((sig.clone(), typ_ctx));
    }
    Err(())
}

fn find_func(
    sess: &Session,
    key1: &FnKey,
    fn_context: &FnContext,
    typ_dict: &TypeDict,
    span: &Span,
) -> TypecheckingResult<FnValue> {
    let mut candidates = fn_context.clone();
    candidates.retain(|key2, _| match (key1, key2) {
        (FnKey::Independent(n1), FnKey::Independent(n2)) => match (n1, n2) {
            (Ident::Original(n1), Ident::Original(n2)) => n1 == n2,
            _ => panic!(),
        },
        (FnKey::Impl(t1, n1), FnKey::Impl(t2, n2)) => {
            equal_types(
                &(
                    (Borrowing::Consumed, span.clone()),
                    (t1.clone(), span.clone()),
                ),
                &(
                    (Borrowing::Consumed, span.clone()),
                    (t2.clone(), span.clone()),
                ),
                typ_dict,
            ) && match (n1, n2) {
                (Ident::Original(n1), Ident::Original(n2)) => n1 == n2,
                _ => panic!(),
            }
        }
        _ => false,
    });
    if candidates.len() == 0 {
        sess.span_err(*span, format!("function {} cannot be found", key1).as_str());
        return Err(());
    }
    if candidates.len() > 1 {
        sess.span_err(
            *span,
            format!("Multiple implementations for function {}", key1).as_str(),
        );
        return Err(());
    }
    for (_, sig) in candidates {
        return Ok(sig);
    }
    Err(())
}

fn find_ident<'a, 'b>(x: &'a Ident, name_context: &'b NameContext) -> &'b Ident {
    match x {
        Ident::Rustspec(_, _) => {
            panic!("trying to lookup in the name context an already translated id")
        }
        Ident::Original(name) => match name_context.get(name) {
            None => panic!("original id not found in name context!"),
            Some(id) => id,
        },
    }
}

fn find_typ<'a, 'b>(x: &'a Ident, var_context: &'b VarContext) -> Option<&'b Typ> {
    match x {
        Ident::Original(_) => panic!("trying to lookup in the var context an original id"),
        Ident::Rustspec(id, _) => var_context.get(id).map(|x| &x.0),
    }
}

fn remove_var(x: &Ident, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Original(_) => panic!("trying to lookup in the var context an original id"),
        Ident::Rustspec(id, _) => var_context.without(id),
    }
}

fn add_var(x: &Ident, typ: &Typ, var_context: &VarContext) -> VarContext {
    match x {
        Ident::Original(_) => panic!("trying to lookup in the var context an original id"),
        Ident::Rustspec(id, name) => var_context.update(id.clone(), (typ.clone(), name.clone())),
    }
}

fn add_name(name: &Ident, var: &Ident, name_context: &NameContext) -> NameContext {
    match name {
        Ident::Original(name) => name_context.update(name.clone(), var.clone()),
        Ident::Rustspec(_, _) => panic!("trying to lookup in the name context a Rustspec id"),
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
    fn_context: &FnContext,
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
                            fn_context,
                            typ_dict,
                            &var_context,
                            name_context,
                        )?;
                    var_context = new_var_context;
                    match arg_typ_borrowing {
                        Borrowing::Borrowed => {
                            sess.span_err(
                                arg.1,
                                "borrowed values are forbidden in Rustspec tuples",
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
            let id = find_ident(id, name_context);
            let new_path = Expression::Named(id.clone());
            match find_typ(id, var_context) {
                None => {
                    sess.span_err(
                        *span,
                        format!(
                            "the variable {} is unknown in context {:?}",
                            id, var_context
                        )
                        .as_str(),
                    );
                    Err(())
                }
                Some(t) => {
                    // This is where linearity kicks in
                    if let Borrowing::Consumed = (t.0).0 {
                        if is_copy(&(t.1).0) {
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
        Expression::Binary((op, op_span), e1, e2) => {
            let (new_e1, t1, var_context) =
                typecheck_expression(sess, e1, fn_context, typ_dict, var_context, name_context)?;
            let (new_e2, t2, var_context) =
                typecheck_expression(sess, e2, fn_context, typ_dict, &var_context, name_context)?;
            match op {
                BinOpKind::Shl | BinOpKind::Shr => match &(t2.1).0 {
                    BaseTyp::Usize => {
                        if is_numeric(&t1) {
                            Ok((
                                Expression::Binary(
                                    (op.clone(), op_span.clone()),
                                    Box::new((new_e1, e1.1.clone())),
                                    Box::new((new_e2, e2.1.clone())),
                                ),
                                t1,
                                var_context,
                            ))
                        } else {
                            sess.span_err(
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
                        sess.span_err(
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
                    if unify_types(&t1, &t2, &HashMap::new()).is_none() {
                        sess.span_err(
                            *span,
                            format!(
                                "wrong types of binary operators, left is {}{} while right is {}{}",
                                t1.0.0, t1.1.0, t2.0.0, t2.1.0
                            )
                            .as_str(),
                        );
                        Err(())
                    } else {
                        if is_numeric(&t1) {
                            Ok((
                                Expression::Binary(
                                    (op.clone(), op_span.clone()),
                                    Box::new((new_e1, e1.1.clone())),
                                    Box::new((new_e2, e2.1.clone())),
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
                            sess.span_err(
                                span.clone(),
                                format!(
                                    "operation only available for numerics, but found type {}{}",
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
        Expression::Unary(op, e1) => {
            let (new_e1, e1_typ, new_var_context) =
                typecheck_expression(sess, e1, fn_context, typ_dict, var_context, name_context)?;
            Ok((
                Expression::Unary(op.clone(), Box::new((new_e1, e1.1.clone()))),
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
        },
        Expression::ArrayIndex((x, x_span), e2) => {
            let x = find_ident(x, name_context);
            let t1 = match find_typ(x, var_context) {
                None => {
                    sess.span_err(*x_span, format!("the variable {} is unknown", x).as_str());
                    return Err(());
                }
                Some(t) => t,
            };
            let (new_e2, t2, var_context) =
                typecheck_expression(sess, e2, fn_context, typ_dict, &var_context, name_context)?;
            // We ignore t1.0 because we can read from both consumed and borrowed array types
            match is_array(sess, t1, typ_dict) {
                Ok((cell_t, cell_t_span)) => {
                    if let Borrowing::Borrowed = (t2.0).0 {
                        sess.span_err(e2.1, "cannot index array with a borrowed type");
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
                            sess.span_err(
                                e2.1,
                                format!(
                                    "expected an integer to index array but got type {}{}",
                                    (t2.0).0,
                                    (t2.1).0
                                )
                                .as_str(),
                            );
                            Err(())
                        }
                    }
                }
                _ => {
                    sess.span_err(
                        *x_span,
                        format!(
                        "this expression should be an array or a sequence but instead has type {}{}",
                        (t1.0).0, (t1.1).0
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
                fn_context,
                &name.1,
            )?;
            let mut typ_var_ctx = typ_var_ctx;
            if let FnValue::ExternalNotInRustspec = f_sig {
                sess.span_err(
                    name.1.clone(),
                    format!(
                        "function {}{} is known but its signature is not in Rustspec",
                        (match prefix {
                            None => String::new(),
                            Some(prefix) => format!("{}::", &prefix.0),
                        }),
                        &name.0
                    )
                    .as_str(),
                );
                return Err(());
            };
            let sig_args = sig_args(&f_sig);
            if sig_args.len() != args.len() {
                sess.span_err(
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
                    fn_context,
                    typ_dict,
                    &var_context,
                    name_context,
                )?;
                var_context = new_var_context;
                let new_arg_borrow = match (&(arg_t.0).0, &arg_borrow) {
                    (Borrowing::Consumed, _) => arg_borrow.clone(),
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_err(*arg_borrow_span, "double borrowing is forbidden in Rust!");
                        return Err(());
                    }
                    (Borrowing::Borrowed, Borrowing::Consumed) => (arg_t.0).0.clone(),
                };
                new_args.push((
                    (new_arg, arg_span.clone()),
                    (new_arg_borrow, arg_borrow_span.clone()),
                ));
                match unify_types(&arg_t, sig_t, &typ_var_ctx) {
                    None => {
                        sess.span_err(
                            *arg_span,
                            format!(
                                "expected type {}{}, got {}{}",
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
            let ret_ty = bind_variable_type(&ret_ty, &typ_var_ctx);
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
            let (new_sel, sel_typ, _) =
                typecheck_expression(sess, &sel, fn_context, typ_dict, &var_context, name_context)?;
            let (f_sig, typ_var_ctx) = find_func(
                sess,
                &FnKey::Impl((sel_typ.1).0.clone(), f.clone()),
                fn_context,
                f_span,
            )?;
            let mut typ_var_ctx = typ_var_ctx;
            if let FnValue::ExternalNotInRustspec = f_sig {
                sess.span_err(
                    *f_span,
                    format!(
                        "function {}::{} is known but its signature is not in Rustspec",
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
            let new_sel_borrow = match (&sel_borrow.0, &(sig_args.first().unwrap().0).0) {
                (Borrowing::Consumed, Borrowing::Borrowed) => {
                    (Borrowing::Borrowed, sel_borrow.1.clone())
                }
                _ => sel_borrow.clone(),
            };
            let mut args = Vec::new();
            args.push((sel.clone(), new_sel_borrow.clone()));
            args.extend(orig_args.clone());
            let mut new_args = Vec::new();
            if sig_args.len() != args.len() {
                sess.span_err(
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
                    fn_context,
                    typ_dict,
                    &var_context,
                    name_context,
                )?;
                var_context = new_var_context;
                let new_arg_t = match (&(arg_t.0).0, &arg_borrow) {
                    (Borrowing::Borrowed, Borrowing::Borrowed) => {
                        sess.span_err(arg_borrow_span, "double borrowing is forbidden in Rust!");
                        return Err(());
                    }
                    (Borrowing::Consumed, Borrowing::Borrowed) => {
                        ((Borrowing::Borrowed, (arg_t.0).1.clone()), arg_t.1.clone())
                    }
                    _ => arg_t.clone(),
                };
                new_args.push((
                    (new_arg, arg_span.clone()),
                    (arg_borrow.clone(), arg_borrow_span.clone()),
                ));
                match unify_types(&new_arg_t, sig_t, &typ_var_ctx) {
                    None => {
                        sess.span_err(
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
            let ret_ty = sig_ret(&f_sig);
            let ret_ty = bind_variable_type(&ret_ty, &typ_var_ctx);
            Ok((
                Expression::MethodCall(
                    Box::new(((new_sel, sel.1.clone()), sel_borrow.clone())),
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
                sess.span_err(*pat_span,
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
            sess.span_err(
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
                Ident::Rustspec(id, name) => (id.clone(), name.clone()),
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
    fn_context: &FnContext,
    typ_dict: &TypeDict,
    var_context: &VarContext,
    name_context: &NameContext,
) -> TypecheckingResult<(Statement, Typ, VarContext, NameContext, VarSet)> {
    match &s {
        Statement::LetBinding((pat, pat_span), typ, ref expr) => {
            let (new_expr, expr_typ, new_var_context) =
                typecheck_expression(sess, expr, fn_context, typ_dict, var_context, name_context)?;
            match typ {
                None => (),
                Some((typ, _)) => {
                    if unify_types(typ, &expr_typ, &HashMap::new()).is_none() {
                        sess.span_err(
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
            let x = find_ident(x, name_context);
            let (new_e, e_typ, new_var_context) =
                typecheck_expression(sess, &e, fn_context, typ_dict, var_context, name_context)?;
            let x_typ = find_typ(x, var_context);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_err(*x_span, "trying to reassign to an inexisting variable");
                    return Err(());
                }
            };
            if unify_types(&e_typ, &x_typ, &HashMap::new()).is_none() {
                sess.span_err(
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
                add_var(x, x_typ, &new_var_context),
                name_context.clone(),
                HashSet::unit(x.clone()),
            ))
        }
        Statement::ArrayUpdate((x, x_span), e1, e2) => {
            let x = find_ident(x, name_context);
            let (new_e1, e1_t, var_context) =
                typecheck_expression(sess, &e1, fn_context, typ_dict, var_context, name_context)?;
            let (new_e2, e2_t, var_context) =
                typecheck_expression(sess, &e2, fn_context, typ_dict, &var_context, name_context)?;
            if !is_index(&(e1_t.1).0) {
                sess.span_err(
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
            let x_typ = find_typ(x, &var_context);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_err(*x_span, "trying to update an inexisting array");
                    return Err(());
                }
            };
            let cell_t = match is_array(sess, x_typ, typ_dict) {
                Ok(cell_t) => cell_t,
                Err(()) => {
                    sess.span_err(
                        *x_span,
                        format!(
                            "{} should be an array but has type {}{}",
                            x,
                            (x_typ.0).0,
                            (x_typ.1).0
                        )
                        .as_str(),
                    );
                    return Err(());
                }
            };
            if unify_types(
                &e2_t,
                &((Borrowing::Consumed, x_span.clone()), cell_t.clone()),
                &HashMap::new(),
            )
            .is_none()
            {
                sess.span_err(
                    e2.1,
                    format!(
                        "array {} has type {}{} but tried to reassign cell with an expression of type {}{}",
                        x, (x_typ.0).0, (x_typ.1).0, (e2_t.0).0, (e2_t.1).0
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
                fn_context,
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
            let (new_cond, cond_t, var_context) =
                typecheck_expression(sess, &cond, fn_context, typ_dict, var_context, name_context)?;
            match cond_t {
                ((Borrowing::Consumed, _), (BaseTyp::Bool, _)) => (),
                _ => sess.span_err(
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
                fn_context,
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
                        fn_context,
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
                    sess.span_err(
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
                            sess.span_err(
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
            let (new_e1, t_e1, var_context) =
                typecheck_expression(sess, e1, fn_context, typ_dict, var_context, name_context)?;
            let (new_e2, t_e2, var_context) =
                typecheck_expression(sess, e2, fn_context, typ_dict, &var_context, name_context)?;
            match &t_e1 {
                ((Borrowing::Consumed, _), (BaseTyp::Usize, _)) => (),
                _ => {
                    sess.span_err(
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
                    sess.span_err(
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
                fn_context,
                typ_dict,
                &var_context,
                &new_name_context,
            )?;
            let mutated_vars = new_b.mutated.as_ref().unwrap().as_ref().vars.clone();
            // Linear variables cannot be consumed in the body of the loop, so we check that
            let var_diff = original_var_context.clone().difference(var_context.clone());
            for (var_diff_id, (_, var_diff_name)) in var_diff {
                if original_var_context.contains_key(&var_diff_id) {
                    sess.span_err(
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
    fn_context: &FnContext,
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
            typecheck_statement(sess, s, fn_context, typ_dict, &var_context, &name_context)?;
        new_stmts.push((new_stmt, s_span));
        var_context = new_var_context;
        name_context = new_name_context;
        mutated_vars = mutated_vars.clone().union(new_mutated_vars);
        if i + 1 < n_stmts {
            // Statement return types should be unit except for the last one
            match stmt_typ {
                ((Borrowing::Consumed, _), (BaseTyp::Unit, _)) => (),
                _ => {
                    sess.span_err(s_span, "statement shoud have an unit type here");
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
    i: Item,
    fn_context: &FnContext,
    typ_dict: &TypeDict,
) -> TypecheckingResult<(Item, FnContext, TypeDict)> {
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
                        fn_context,
                        typ_dict,
                        &var_context,
                        &name_context,
                    )?
                    .0,
                    b_span.clone(),
                ),
            );
            let fn_context =
                fn_context.update(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
            Ok((out, fn_context, typ_dict.clone()))
        }
        Item::ArrayDecl(id, size, cell_t) => Ok((
            i.clone(),
            fn_context.clone(),
            typ_dict.update(
                match &id.0 {
                    Ident::Original(s) => s.clone(),
                    Ident::Rustspec(_, _) => panic!(),
                },
                (
                    (Borrowing::Consumed, id.1.clone()),
                    (
                        BaseTyp::Array(size.clone(), Box::new(cell_t.clone())),
                        id.1.clone(),
                    ),
                ),
            ),
        )),
    }
}

pub fn typecheck_program(
    sess: &Session,
    p: Program,
    external_funcs: &HashMap<FnKey, Option<ExternalFuncSig>>,
    _allowed_sigs: &AllowedSigs,
) -> TypecheckingResult<Program> {
    let mut fn_context: FnContext = external_funcs
        .iter()
        .map(|(k, v)| {
            (
                k.clone(),
                match v {
                    Some(v) => FnValue::External(v.clone()),
                    None => FnValue::ExternalNotInRustspec,
                },
            )
        })
        .collect();
    let mut typ_dict = HashMap::new();
    Ok(Program {
        items: check_vec(
            p.items
                .into_iter()
                .map(|(i, i_span)| {
                    let (new_i, new_fn_context, new_typ_dict) =
                        typecheck_item(sess, i, &fn_context, &typ_dict)?;
                    fn_context = new_fn_context;
                    typ_dict = new_typ_dict;
                    Ok((new_i, i_span))
                })
                .collect(),
        )?,
        imported_crates: p.imported_crates,
    })
}
