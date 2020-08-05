use crate::rustspec::*;
use im::{HashMap, HashSet};
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;

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
        // TODO: implement special cases for derived copy
        BaseTyp::Named(_) => false,
        BaseTyp::Tuple(ts) => ts.iter().all(|(t, _)| is_copy(t)),
    }
}

fn is_array(t: &BaseTyp) -> Option<&Spanned<BaseTyp>> {
    match t {
        BaseTyp::Seq(t1) => Some(&t1),
        //TODO: add named array types
        _ => None,
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

fn equal_types(t1: &Typ, t2: &Typ) -> bool {
    match (&(t1.0).0, &(t2.0).0) {
        (Borrowing::Consumed, Borrowing::Consumed) | (Borrowing::Borrowed, Borrowing::Borrowed) => {
            match (&(t1.1).0, &(t2.1).0) {
                (BaseTyp::Unit, BaseTyp::Unit) => true,
                (BaseTyp::Bool, BaseTyp::Bool) => true,
                (BaseTyp::UInt128, BaseTyp::UInt128) => true,
                (BaseTyp::Int128, BaseTyp::Int128) => true,
                (BaseTyp::UInt64, BaseTyp::UInt64) => true,
                (BaseTyp::Int64, BaseTyp::Int64) => true,
                (BaseTyp::UInt32, BaseTyp::UInt32) => true,
                (BaseTyp::Int32, BaseTyp::Int32) => true,
                (BaseTyp::UInt16, BaseTyp::UInt16) => true,
                (BaseTyp::Int16, BaseTyp::Int16) => true,
                (BaseTyp::UInt8, BaseTyp::UInt8) => true,
                (BaseTyp::Int8, BaseTyp::Int8) => true,
                (BaseTyp::Usize, BaseTyp::Usize) => true,
                (BaseTyp::Isize, BaseTyp::Isize) => true,
                (BaseTyp::Seq(tc1), BaseTyp::Seq(tc2)) => equal_types(
                    &(((Borrowing::Consumed, (t1.1).1)), *tc1.clone()),
                    &(((Borrowing::Consumed, (t2.1).1)), *tc2.clone()),
                ),
                (BaseTyp::Named(p1), BaseTyp::Named(p2)) => {
                    p1.location.len() == p2.location.len()
                        && (p1
                            .location
                            .iter()
                            .zip(p2.location.iter())
                            .all(|(i1, i2)| i1 == i2))
                        && match (&p1.arg, &p2.arg) {
                            (None, None) => true,
                            (Some(tc1), Some(tc2)) => equal_types(
                                &(((Borrowing::Consumed, (t1.1).1)), (*tc1.clone(), (t1.1).1)),
                                &(((Borrowing::Consumed, (t2.1).1)), (*tc2.clone(), (t2.1).1)),
                            ),
                            _ => false,
                        }
                }
                (BaseTyp::Tuple(ts1), BaseTyp::Tuple(ts2)) => {
                    ts1.len() == ts2.len()
                        && ts1.iter().zip(ts2.iter()).all(|(tc1, tc2)| {
                            equal_types(
                                &(((Borrowing::Consumed, (t1.1).1)), tc1.clone()),
                                &(((Borrowing::Consumed, (t2.1).1)), tc2.clone()),
                            )
                        })
                }
                _ => false,
            }
        }
        _ => false,
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum FnKey {
    Static(Ident),
    Method(BaseTyp, Ident),
}

type FnContext = HashMap<FnKey, FuncSig>;

type VarContext = HashMap<Ident, Typ>;

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
    var_context: &VarContext,
) -> TypecheckingResult<(Typ, VarContext)> {
    match e {
        Expression::Tuple(args) => {
            let mut var_context = var_context.clone();
            let typ_args = args
                .iter()
                .map(|arg| {
                    let (((arg_typ_borrowing, _), arg_typ), new_var_context) =
                        typecheck_expression(sess, arg, fn_context, &var_context)?;
                    var_context = new_var_context;
                    match arg_typ_borrowing {
                        Borrowing::Borrowed => {
                            sess.span_err(
                                arg.1,
                                "borrowed values are forbidden in Rustspec tuples",
                            );
                            Err(())
                        }
                        Borrowing::Consumed => Ok(arg_typ),
                    }
                })
                .collect();
            let typ_args = check_vec(typ_args)?;
            Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Tuple(typ_args), span.clone()),
                ),
                var_context,
            ))
        }
        Expression::Named(path) => match (path.arg.as_ref(), path.location.len()) {
            (None, 1) => {
                let (id, _) = &path.location[0];
                match var_context.get(id) {
                    None => {
                        sess.span_err(*span, format!("the variable {} is unknown", id).as_str());
                        Err(())
                    }
                    Some(t) => {
                        // This is where linearity kicks in
                        if let Borrowing::Consumed = (t.0).0 {
                            if is_copy(&(t.1).0) {
                                Ok((t.clone(), var_context.clone()))
                            } else {
                                let new_var_context = var_context.without(&id);
                                Ok((t.clone(), new_var_context))
                            }
                        } else {
                            Ok((t.clone(), var_context.clone()))
                        }
                    }
                }
            }
            _ => {
                sess.span_err(*span, format!("the variable {} is unknown", path).as_str());
                Err(())
            }
        },
        Expression::Binary((op, _), e1, e2) => {
            let (t1, var_context) = typecheck_expression(sess, e1, fn_context, var_context)?;
            let (t2, var_context) = typecheck_expression(sess, e2, fn_context, &var_context)?;
            // TODO: do special thing for shift
            if !equal_types(&t1, &t2) {
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
                Ok((
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
            }
        }
        Expression::Unary(_, e1) => typecheck_expression(sess, e1, fn_context, var_context),
        Expression::Lit(lit) => match lit {
            Literal::Bool(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Bool, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int128(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int128, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt128(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt128, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int64(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int64, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt64(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt64, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int32(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int32, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt32(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt32, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int16(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int16, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt16(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt16, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Int8(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Int8, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::UInt8(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::UInt8, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Usize(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Usize, span.clone()),
                ),
                var_context.clone(),
            )),
            Literal::Isize(_) => Ok((
                (
                    (Borrowing::Consumed, span.clone()),
                    (BaseTyp::Isize, span.clone()),
                ),
                var_context.clone(),
            )),
        },
        Expression::ArrayIndex((x, x_span), e2) => {
            let t1 = match var_context.get(&x) {
                None => {
                    sess.span_err(*x_span, format!("the variable {} is unknown", x).as_str());
                    return Err(());
                }
                Some(t) => t,
            };
            let (t2, var_context) = typecheck_expression(sess, e2, fn_context, &var_context)?;
            // We ignore t1.0 because we can read from both consumed and borrowed array types
            match &(t1.1).0 {
                BaseTyp::Seq(seq_t) => {
                    let (cell_t, cell_t_span) = (&seq_t.0, &seq_t.1);
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
                //TODO: add named arrays
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
        Expression::FuncCall((f, f_span), args) => match (f.arg.as_ref(), f.location.len()) {
            (None, 1) => {
                let (id, _) = &f.location[0];
                let f_sig = match fn_context.get(&FnKey::Static(id.clone())) {
                    None => {
                        sess.span_err(*f_span, format!("unknown function {}", f).as_str());
                        return Err(());
                    }
                    Some(sig) => sig,
                };
                if f_sig.args.len() != args.len() {
                    sess.span_err(
                        *span,
                        format!(
                            "function {} was expecting {} arguments but got {}",
                            f,
                            f_sig.args.len(),
                            args.len()
                        )
                        .as_str(),
                    )
                }
                let mut var_context = var_context.clone();
                for ((_, (sig_t, _)), (arg, arg_span)) in f_sig.args.iter().zip(args) {
                    let (arg_t, new_var_context) = typecheck_expression(
                        sess,
                        &(arg.clone(), arg_span.clone()),
                        fn_context,
                        &var_context,
                    )?;
                    var_context = new_var_context;
                    match ((arg_t.0).0, &sig_t.0) {
                        (Borrowing::Consumed, &(Borrowing::Borrowed, _)) => {
                            sess.span_err(*arg_span, "expected a borrow here but didn't find one");
                            return Err(());
                        }
                        (Borrowing::Borrowed, &(Borrowing::Consumed, _)) => {
                            sess.span_err(
                                *arg_span,
                                "superflous borrow here, argument is consumed",
                            );
                            return Err(());
                        }
                        _ => (),
                    }
                    if (arg_t.1).0 != (sig_t.1).0 {
                        sess.span_err(
                            *arg_span,
                            format!("expected type {}, got {}", (sig_t.1).0, (arg_t.1).0).as_str(),
                        );
                        return Err(());
                    }
                }
                Ok((
                    ((Borrowing::Consumed, *f_span), f_sig.ret.clone()),
                    var_context,
                ))
            }
            _ => {
                sess.span_err(
                    *f_span,
                    "calling foreign functions not supported for now in Rustspec",
                );
                Err(())
            }
        },
        Expression::MethodCall(sel, _, (f, f_span), args) => {
            let mut var_context = var_context.clone();
            let (sel_typ, new_var_context) =
                typecheck_expression(sess, &sel, fn_context, &var_context)?;
            var_context = new_var_context;
            let f_sig = match fn_context.get(&FnKey::Method((sel_typ.1).0.clone(), f.clone())) {
                None => {
                    sess.span_err(
                        *f_span,
                        format!("unknown method {}::{}", (sel_typ.1).0, f).as_str(),
                    );
                    return Err(());
                }
                Some(sig) => sig,
            };
            let mut args = args.clone();
            args.push(*sel.clone());
            if f_sig.args.len() != args.len() {
                sess.span_err(
                    *span,
                    format!(
                        "method {}::{} was expecting {} arguments but got {}",
                        (sel_typ.1).0,
                        f,
                        f_sig.args.len(),
                        args.len()
                    )
                    .as_str(),
                )
            }
            for ((_, (sig_t, _)), (ref arg, arg_span)) in f_sig.args.iter().zip(args) {
                let (arg_t, new_var_context) = typecheck_expression(
                    sess,
                    &(arg.clone(), arg_span.clone()),
                    fn_context,
                    &var_context,
                )?;
                var_context = new_var_context;
                match (arg_t.0, &sig_t.0) {
                    ((Borrowing::Consumed, _), &(Borrowing::Borrowed, _)) => {
                        sess.span_err(arg_span, "expected a borrow here but didn't find one");
                        return Err(());
                    }
                    ((Borrowing::Borrowed, _), &(Borrowing::Consumed, _)) => {
                        sess.span_err(arg_span, "superflous borrow here, argument is consumed");
                        return Err(());
                    }
                    _ => (),
                }
                if (arg_t.1).0 != (sig_t.1).0 {
                    sess.span_err(
                        arg_span,
                        format!("expected type {}, got {}", (sig_t.1).0, (arg_t.1).0).as_str(),
                    );
                    return Err(());
                }
            }
            Ok((
                ((Borrowing::Consumed, *f_span), f_sig.ret.clone()),
                var_context,
            ))
        }
    }
}

fn typecheck_pattern(
    sess: &Session,
    (pat, pat_span): &Spanned<Pattern>,
    (borrowing_typ, typ): &Typ,
) -> TypecheckingResult<VarContext> {
    match (pat, &typ.0) {
        (Pattern::Tuple(pat_args), BaseTyp::Tuple(ref typ_args)) => {
            if pat_args.len() != typ_args.len() {
                sess.span_err(*pat_span,
                    format!("let-binding tuple pattern has {} variables but {} were expected from the type",
                     pat_args.len(),
                     typ_args.len()).as_str()
                )
            };
            pat_args.iter().zip(typ_args.iter()).fold(
                Ok(HashMap::new()),
                |acc, (pat_arg, typ_arg)| {
                    let sub_var_context = typecheck_pattern(
                        sess,
                        pat_arg,
                        &((Borrowing::Consumed, *pat_span), typ_arg.clone()),
                    )?;
                    Ok(acc?.union(sub_var_context))
                },
            )
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
        (Pattern::WildCard, _) => Ok(HashMap::new()),
        (Pattern::IdentPat(x), _) => Ok(HashMap::unit(
            x.clone(),
            (borrowing_typ.clone(), typ.clone()),
        )),
    }
}

fn typecheck_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    fn_context: &FnContext,
    var_context: &VarContext,
) -> TypecheckingResult<(Statement, Typ, VarContext, VarSet)> {
    match &s {
        Statement::LetBinding((pat, pat_span), typ, ref expr) => {
            let (expr_typ, new_var_context) =
                typecheck_expression(sess, expr, fn_context, var_context)?;
            match typ {
                None => (),
                Some((typ, _)) => {
                    if !equal_types(typ, &expr_typ) {
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
            let pat_var_context =
                typecheck_pattern(sess, &(pat.clone(), pat_span.clone()), &expr_typ)?;
            Ok((
                s.clone(),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                new_var_context.clone().union(pat_var_context),
                HashSet::new(),
            ))
        }
        Statement::Reassignment((x, x_span), e) => {
            let (e_typ, new_var_context) = typecheck_expression(sess, &e, fn_context, var_context)?;
            let x_typ = var_context.get(&x);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_err(*x_span, "trying to reassign to an inexisting variable");
                    return Err(());
                }
            };
            if !equal_types(&e_typ, &x_typ) {
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
                s.clone(),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                new_var_context.clone().update(x.clone(), x_typ.clone()),
                HashSet::unit(x.clone()),
            ))
        }
        Statement::ArrayUpdate((x, x_span), e1, e2) => {
            let (e1_t, var_context) = typecheck_expression(sess, &e1, fn_context, var_context)?;
            let (e2_t, var_context) = typecheck_expression(sess, &e2, fn_context, &var_context)?;
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
            let x_typ = var_context.get(&x);
            let x_typ = match x_typ {
                Some(t) => t,
                None => {
                    sess.span_err(*x_span, "trying to updated an inexisting array");
                    return Err(());
                }
            };
            let cell_t = match is_array(&(x_typ.1).0) {
                Some(cell_t) => cell_t,
                None => {
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
            if !equal_types(
                &e2_t,
                &((Borrowing::Consumed, x_span.clone()), cell_t.clone()),
            ) {
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
                s.clone(),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                var_context,
                HashSet::unit(x.clone()),
            ))
        }
        Statement::ReturnExp(e) => {
            let (e_t, var_context) =
                typecheck_expression(sess, &(e.clone(), s_span), fn_context, var_context)?;
            Ok((s.clone(), e_t, var_context, HashSet::new()))
        }
        Statement::Conditional(cond, (b1, b1_span), b2) => {
            let original_var_context = var_context;
            let (cond_t, var_context) = typecheck_expression(sess, &cond, fn_context, var_context)?;
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
                &var_context,
            )?;
            let (new_b2, var_context_b2) = match b2 {
                None => (None, var_context.clone()),
                Some((b2, b2_span)) => {
                    let (new_b2, var_context_b2) = typecheck_block(
                        sess,
                        (b2.clone(), b2_span.clone()),
                        fn_context,
                        &var_context,
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
            let new_mutated = match &new_b1.mutated_vars {
                None => HashSet::new(),
                Some(m) => m.clone(),
            }
            .union(match &new_b2 {
                None => HashSet::new(),
                Some((new_b2, _)) => match &new_b2.mutated_vars {
                    None => HashSet::new(),
                    Some(m) => m.clone(),
                },
            });
            Ok((
                Statement::Conditional(cond.clone(), (new_b1, *b1_span), new_b2),
                ((Borrowing::Consumed, s_span), (BaseTyp::Unit, s_span)),
                original_var_context
                    .clone()
                    .intersection(var_context_b1)
                    .intersection(var_context_b2),
                new_mutated,
            ))
        }
        Statement::ForLoop((x, x_span), e1, e2, (b, b_span)) => {
            let original_var_context = var_context;
            let (t_e1, var_context) = typecheck_expression(sess, e1, fn_context, var_context)?;
            let (t_e2, var_context) = typecheck_expression(sess, e2, fn_context, &var_context)?;
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
            let var_context = var_context.update(
                x.clone(),
                ((Borrowing::Consumed, *x_span), (BaseTyp::Usize, *x_span)),
            );
            let (new_b, var_context) =
                typecheck_block(sess, (b.clone(), b_span.clone()), fn_context, &var_context)?;
            let mutated_vars = new_b.mutated_vars.clone().unwrap();
            Ok((
                Statement::ForLoop(
                    (x.clone(), *x_span),
                    e1.clone(),
                    e2.clone(),
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
    fn_context: &FnContext,
    original_var_context: &VarContext,
) -> TypecheckingResult<(Block, VarContext)> {
    let mut var_context = original_var_context.clone();
    let mut mutated_vars = HashSet::new();
    let mut return_typ = None;
    let mut new_stmts = Vec::new();
    let n_stmts = b.stmts.len();
    for (i, s) in b.stmts.into_iter().enumerate() {
        let s_span = s.1.clone();
        let (new_stmt, stmt_typ, new_var_context, new_mutated_vars) =
            typecheck_statement(sess, s, fn_context, &var_context)?;
        new_stmts.push((new_stmt, s_span));
        var_context = new_var_context;
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
    let mut_tuple = Some(Box::new(Statement::ReturnExp(Expression::Tuple(
        mutated_vars
            .iter()
            .map(|i| {
                (
                    Expression::Named(Path {
                        location: vec![(i.clone(), b_span.clone())],
                        arg: None,
                    }),
                    b_span.clone(),
                )
            })
            .collect(),
    ))));
    Ok((
        Block {
            stmts: new_stmts,
            mutated_vars: Some(mutated_vars),
            mutated_vars_tuple: mut_tuple,
            return_typ,
        },
        var_context.intersection(original_var_context.clone()),
    ))
}

fn typecheck_item(
    sess: &Session,
    i: Item,
    fn_context: &FnContext,
) -> TypecheckingResult<(Item, FnContext)> {
    match i {
        Item::FnDecl((f, f_span), sig, (b, b_span)) => {
            let var_context = HashMap::new();
            let var_context = sig
                .args
                .iter()
                .fold(var_context, |var_context, ((x, _), (t, _))| {
                    var_context.update(x.clone(), t.clone())
                });
            let out = Item::FnDecl(
                (f.clone(), f_span),
                sig.clone(),
                (
                    typecheck_block(sess, (b, b_span), fn_context, &var_context)?.0,
                    b_span,
                ),
            );
            let fn_context = fn_context.update(FnKey::Static(f), sig);
            Ok((out, fn_context))
        }
        // TODO: Collect uses and put them in context
        Item::Use(ref _p) => Ok((i, fn_context.clone())),
    }
}

pub fn typecheck_program(sess: &Session, p: Program) -> TypecheckingResult<Program> {
    let mut fn_context = HashMap::new();
    check_vec(
        p.into_iter()
            .map(|(i, i_span)| {
                let (new_i, new_fn_context) = typecheck_item(sess, i, &fn_context)?;
                fn_context = new_fn_context;
                Ok((new_i, i_span))
            })
            .collect(),
    )
}
