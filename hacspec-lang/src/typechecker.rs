use crate::rustspec::*;
use im::{HashMap, HashSet};
use rustc_session::Session;

use itertools::Itertools;
use rustc_span::symbol::Ident;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ComputedBaseTyp {
    Unit,
    Bool,
    UInt128,
    Int128,
    UInt64,
    Int64,
    UInt32,
    Int32,
    UInt16,
    Int16,
    UInt8,
    Int8,
    Usize,
    Isize,
    Seq(Box<ComputedBaseTyp>),
    Named(Path),
    Tuple(Vec<ComputedBaseTyp>),
}

fn base_typ_to_computed(t: &BaseTyp) -> ComputedBaseTyp {
    match t {
        BaseTyp::Unit => ComputedBaseTyp::Unit,
        BaseTyp::Bool => ComputedBaseTyp::Bool,
        BaseTyp::UInt128 => ComputedBaseTyp::UInt128,
        BaseTyp::Int128 => ComputedBaseTyp::Int128,
        BaseTyp::UInt64 => ComputedBaseTyp::UInt64,
        BaseTyp::Int64 => ComputedBaseTyp::Int64,
        BaseTyp::UInt32 => ComputedBaseTyp::UInt32,
        BaseTyp::Int32 => ComputedBaseTyp::Int32,
        BaseTyp::UInt16 => ComputedBaseTyp::UInt16,
        BaseTyp::Int16 => ComputedBaseTyp::Int16,
        BaseTyp::UInt8 => ComputedBaseTyp::UInt8,
        BaseTyp::Int8 => ComputedBaseTyp::Int8,
        BaseTyp::Usize => ComputedBaseTyp::Usize,
        BaseTyp::Isize => ComputedBaseTyp::Isize,
        BaseTyp::Seq(t1) => ComputedBaseTyp::Seq(Box::new(base_typ_to_computed(&t1.0))),
        BaseTyp::Named(path) => ComputedBaseTyp::Named(path.clone()),
        BaseTyp::Tuple(ts) => ComputedBaseTyp::Tuple(
            ts.into_iter()
                .map(|(arg, _)| base_typ_to_computed(arg))
                .collect(),
        ),
    }
}

fn is_copy(t: &ComputedBaseTyp) -> bool {
    match t {
        ComputedBaseTyp::Unit => true,
        ComputedBaseTyp::Bool => true,
        ComputedBaseTyp::UInt128 => true,
        ComputedBaseTyp::Int128 => true,
        ComputedBaseTyp::UInt64 => true,
        ComputedBaseTyp::Int64 => true,
        ComputedBaseTyp::UInt32 => true,
        ComputedBaseTyp::Int32 => true,
        ComputedBaseTyp::UInt16 => true,
        ComputedBaseTyp::Int16 => true,
        ComputedBaseTyp::UInt8 => true,
        ComputedBaseTyp::Int8 => true,
        ComputedBaseTyp::Usize => true,
        ComputedBaseTyp::Isize => true,
        ComputedBaseTyp::Seq(_) => false,
        // TODO: implement special cases for derived copy
        ComputedBaseTyp::Named(_) => false,
        ComputedBaseTyp::Tuple(ts) => ts.iter().all(|t| is_copy(t)),
    }
}

impl fmt::Display for ComputedBaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ComputedBaseTyp::Unit => write!(f, "unit"),
            ComputedBaseTyp::Bool => write!(f, "bool"),
            ComputedBaseTyp::UInt128 => write!(f, "u128"),
            ComputedBaseTyp::Int128 => write!(f, "i128"),
            ComputedBaseTyp::UInt64 => write!(f, "u64"),
            ComputedBaseTyp::Int64 => write!(f, "i64"),
            ComputedBaseTyp::UInt32 => write!(f, "u32"),
            ComputedBaseTyp::Int32 => write!(f, "i32"),
            ComputedBaseTyp::UInt16 => write!(f, "u16"),
            ComputedBaseTyp::Int16 => write!(f, "i16"),
            ComputedBaseTyp::UInt8 => write!(f, "u8"),
            ComputedBaseTyp::Int8 => write!(f, "i8"),
            ComputedBaseTyp::Usize => write!(f, "usize"),
            ComputedBaseTyp::Isize => write!(f, "isize"),
            ComputedBaseTyp::Seq(mu) => {
                let mu = &*mu;
                write!(f, "Seq<{}>", mu)
            }
            ComputedBaseTyp::Named(path) => write!(f, "{}", path),
            ComputedBaseTyp::Tuple(args) => write!(
                f,
                "({})",
                args.iter().map(|arg| format!("{}", arg)).format(", ")
            ),
        }
    }
}

type ComputedTyp = (Borrowing, ComputedBaseTyp);

#[derive(Clone, PartialEq, Eq, Hash)]
enum FnKey {
    Static(Ident),
    Method(ComputedTyp, Ident)
}

type FnContext = HashMap<FnKey, FuncSig>;

type VarContext = HashMap<Ident, ComputedTyp>;

type VarSet = HashSet<Ident>;

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
) -> TypecheckingResult<(ComputedTyp, VarContext)> {
    match e {
        Expression::Tuple(args) => {
            let mut var_context = var_context.clone();
            let typ_args = args
                .iter()
                .map(|arg| {
                    let ((arg_typ_borrowing, arg_typ), new_var_context) =
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
                (Borrowing::Consumed, ComputedBaseTyp::Tuple(typ_args)),
                var_context,
            ))
        }
        Expression::Named(path) => match (path.arg.as_ref(), path.location.len()) {
            (None, 1) => {
                let id = path.location[0];
                match var_context.get(&id) {
                    None => {
                        sess.span_err(*span, format!("the variable {} is unknown", id).as_str());
                        Err(())
                    }
                    Some(t) => {
                        // This is where linearity kicks in
                        if t.0 == Borrowing::Borrowed || is_copy(&t.1) {
                            Ok((t.clone(), var_context.clone()))
                        } else {
                            let new_var_context = var_context.without(&id);
                            Ok((t.clone(), new_var_context))
                        }
                    }
                }
            }
            _ => {
                sess.span_err(*span, format!("the variable {} is unknown", path).as_str());
                Err(())
            }
        },
        Expression::Binary(_, e1, e2) => {
            let (t1, var_context) = typecheck_expression(sess, e1, fn_context, var_context)?;
            let (t2, var_context) = typecheck_expression(sess, e2, fn_context, &var_context)?;
            if t1 != t2 {
                sess.span_err(
                    *span,
                    format!(
                        "wrong types of binary operators, left is {}{} while right is {}{}",
                        t1.0, t1.1, t2.0, t2.1
                    )
                    .as_str(),
                );
                Err(())
            } else {
                Ok((t1, var_context))
            }
        }
        Expression::Unary(_, e1) => typecheck_expression(sess, e1, fn_context, var_context),
        Expression::Lit(lit) => match lit {
            Literal::Bool(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Bool),
                var_context.clone(),
            )),
            Literal::Int128(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Int128),
                var_context.clone(),
            )),
            Literal::UInt128(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::UInt128),
                var_context.clone(),
            )),
            Literal::Int64(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Int64),
                var_context.clone(),
            )),
            Literal::UInt64(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::UInt64),
                var_context.clone(),
            )),
            Literal::Int32(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Int32),
                var_context.clone(),
            )),
            Literal::UInt32(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::UInt32),
                var_context.clone(),
            )),
            Literal::Int16(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Int16),
                var_context.clone(),
            )),
            Literal::UInt16(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::UInt16),
                var_context.clone(),
            )),
            Literal::Int8(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Int8),
                var_context.clone(),
            )),
            Literal::UInt8(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::UInt8),
                var_context.clone(),
            )),
            Literal::Usize(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Usize),
                var_context.clone(),
            )),
            Literal::Isize(_) => Ok((
                (Borrowing::Consumed, ComputedBaseTyp::Isize),
                var_context.clone(),
            )),
        },
        Expression::ArrayIndex(e1, e2) => {
            let (t1, var_context) = typecheck_expression(sess, e1, fn_context, var_context)?;
            let (t2, var_context) = typecheck_expression(sess, e2, fn_context, &var_context)?;
            // We ignore t1.0 because we can read from both consumed and borrowed array types
            match t1.1 {
                ComputedBaseTyp::Seq(cell_t) => {
                    if let Borrowing::Borrowed = t2.0 {
                        sess.span_err(e2.1, "cannot index array with a borrowed type");
                        return Err(());
                    }
                    match t2.1 {
                        ComputedBaseTyp::UInt128
                        | ComputedBaseTyp::Int128
                        | ComputedBaseTyp::UInt64
                        | ComputedBaseTyp::Int64
                        | ComputedBaseTyp::UInt32
                        | ComputedBaseTyp::Int32
                        | ComputedBaseTyp::UInt16
                        | ComputedBaseTyp::Int16
                        | ComputedBaseTyp::UInt8
                        | ComputedBaseTyp::Int8
                        | ComputedBaseTyp::Usize
                        | ComputedBaseTyp::Isize => {
                            Ok(((Borrowing::Consumed, *cell_t), var_context))
                        }
                        _ => {
                            sess.span_err(
                                e2.1,
                                format!(
                                    "expected an integer to index array but got type {}{}",
                                    t2.0, t2.1
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
                        e1.1,
                        format!(
                        "this expression should be an array or a sequence but instead has type {}{}",
                        t1.0, t1.1
                    )
                        .as_str(),
                    );
                    Err(())
                }
            }
        }
        Expression::FuncCall((f, f_span), args) => match (f.arg.as_ref(), f.location.len()) {
            (None, 1) => {
                let id = f.location[0];
                let f_sig = match fn_context.get(&FnKey::Static(id)) {
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
                    match (arg_t.0, &sig_t.0) {
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
                    if arg_t.1 != base_typ_to_computed(&sig_t.1.0) {
                        sess.span_err(*arg_span,
                            format!("expected type {}, got {}",
                                base_typ_to_computed(&sig_t.1.0), arg_t.1
                            ).as_str()
                        );
                        return Err(());
                    }
                }
                Ok(((Borrowing::Consumed, base_typ_to_computed(&f_sig.ret.0)), var_context))
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
            let (sel_typ, new_var_context) = typecheck_expression(sess, &sel, fn_context, &var_context)?;
            var_context = new_var_context;
            let f_sig = match fn_context.get(&FnKey::Method(sel_typ.clone(), *f)) {
                None => {
                    sess.span_err(*f_span, format!("unknown method {}::{}", sel_typ.1, f).as_str());
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
                        sel_typ.1, f,
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
                    (Borrowing::Consumed, &(Borrowing::Borrowed, _)) => {
                        sess.span_err(arg_span, "expected a borrow here but didn't find one");
                        return Err(());
                    }
                    (Borrowing::Borrowed, &(Borrowing::Consumed, _)) => {
                        sess.span_err(
                            arg_span,
                            "superflous borrow here, argument is consumed",
                        );
                        return Err(());
                    }
                    _ => (),
                }
                if arg_t.1 != base_typ_to_computed(&sig_t.1.0) {
                    sess.span_err(arg_span,
                        format!("expected type {}, got {}",
                            base_typ_to_computed(&sig_t.1.0), arg_t.1
                        ).as_str()
                    );
                    return Err(());
                }
            }
            Ok(((Borrowing::Consumed, base_typ_to_computed(&f_sig.ret.0)), var_context))
        }
    }
}

fn typecheck_pattern(
    sess: &Session,
    (pat, pat_span): &Spanned<Pattern>,
    (borrowing_typ, typ): &ComputedTyp,
) -> TypecheckingResult<VarContext> {
    match (pat, typ) {
        (Pattern::Tuple(pat_args), ComputedBaseTyp::Tuple(typ_args)) => {
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
                    let sub_var_context =
                        typecheck_pattern(sess, pat_arg, &(Borrowing::Consumed, typ_arg.clone()))?;
                    Ok(acc?.union(sub_var_context))
                },
            )
        }
        (Pattern::Tuple(_), _) => {
            sess.span_err(
                *pat_span,
                format!(
                    "let-binding pattern expected a tuple but the type is {}",
                    typ
                )
                .as_str(),
            );
            Err(())
        }
        (Pattern::WildCard, _) => Ok(HashMap::new()),
        (Pattern::IdentPat(x, _), _) => Ok(HashMap::unit(*x, (borrowing_typ.clone(), typ.clone()))),
    }
}

fn typecheck_statement(
    sess: &Session,
    s: &Statement,
    fn_context: &FnContext,
    var_context: &VarContext,
) -> TypecheckingResult<(VarContext, VarSet)> {
    match s {
        Statement::LetBinding((pat, pat_span), typ, expr) => {
            let ((expr_typ_borrowing, expr_typ), new_var_context) =
                typecheck_expression(sess, expr, fn_context, var_context)?;
            match typ {
                None => (),
                Some((((borrow_typ, _), (typ, _)), _)) => {
                    if (borrow_typ, &base_typ_to_computed(&typ))
                        != (&expr_typ_borrowing, &expr_typ)
                    {
                        sess.span_err(
                            *pat_span,
                            format!(
                                "wrong type declared for variable: expected {}, found {}",
                                typ, expr_typ
                            )
                            .as_str(),
                        );
                        return Err(());
                    }
                }
            };
            let pat_var_context = typecheck_pattern(
                sess,
                &(pat.clone(), pat_span.clone()),
                &(expr_typ_borrowing, expr_typ),
            )?;
            Ok((
                new_var_context.clone().union(pat_var_context),
                HashSet::new(),
            ))
        }
        _ => unimplemented!(),
    }
}

fn typecheck_block(
    sess: &Session,
    b: Block,
    fn_context: &FnContext,
    var_context: &VarContext,
) -> TypecheckingResult<Block> {
    let mut var_context = var_context.clone();
    let mut mutated_vars = HashSet::new();
    for (s, _) in b.stmts.iter() {
        let (new_var_context, new_mutated_vars) =
            typecheck_statement(sess, s, fn_context, &var_context)?;
        var_context = new_var_context;
        mutated_vars = mutated_vars.clone().union(new_mutated_vars)
    }
    let mutated_vars = None;
    let return_typ = None;
    // We don't return a new VarContext because the block is the scope of the variables
    // defined inside it.
    Ok(Block {
        stmts: b.stmts,
        mutated_vars,
        return_typ,
    })
}

fn typecheck_item(
    sess: &Session,
    i: Item,
    fn_context: &FnContext,
) -> TypecheckingResult<(Item, FnContext)> {
    match i {
        Item::FnDecl(f, sig, (b, b_span)) => {
            let var_context = HashMap::new();
            let var_context = sig.args.iter().fold(
                var_context,
                |var_context, ((x, _), (((t_b, _), (t, _)), _))| {
                    var_context.update(*x, (t_b.clone(), base_typ_to_computed(&t)))
                },
            );
            let out = Item::FnDecl(
                f,
                sig.clone(),
                (typecheck_block(sess, b, fn_context, &var_context)?, b_span),
            );
            let fn_context = fn_context.update(FnKey::Static(f), sig);
            Ok((out, fn_context))
        }
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
