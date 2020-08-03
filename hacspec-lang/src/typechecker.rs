use crate::rustspec::*;
use im::{HashMap, HashSet};
use rustc_session::Session;

use itertools::Itertools;
use rustc_span::symbol::Ident;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
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

fn base_typ_to_computed(t: BaseTyp) -> ComputedBaseTyp {
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
        BaseTyp::Seq(t1) => ComputedBaseTyp::Seq(Box::new(base_typ_to_computed((*t1).0))),
        BaseTyp::Named(path) => ComputedBaseTyp::Named(path),
        BaseTyp::Tuple(ts) => ComputedBaseTyp::Tuple(
            ts.into_iter()
                .map(|(arg, _)| base_typ_to_computed(arg))
                .collect(),
        ),
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

type FnContext = HashMap<Ident, FuncSig>;

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
) -> TypecheckingResult<ComputedTyp> {
    match e {
        Expression::Tuple(args) => {
            let typ_args = args
                .iter()
                .map(|arg| {
                    let (arg_typ_borrowing, arg_typ) =
                        typecheck_expression(sess, arg, fn_context, var_context)?;
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
            Ok((Borrowing::Consumed, ComputedBaseTyp::Tuple(typ_args)))
        }
        Expression::Named(path) => match (path.arg.as_ref(), path.location.len()) {
            (None, 1) => {
                let id = path.location[0];
                match var_context.get(&id) {
                    None => {
                        sess.span_err(*span, format!("the variable {} is unknown", id).as_str());
                        Err(())
                    }
                    Some(t) => Ok(t.clone()),
                }
            }
            _ => {
                sess.span_err(*span, format!("the variable {} is unknown", path).as_str());
                Err(())
            }
        },
        _ => unimplemented!(),
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
            let (expr_typ_borrowing, expr_typ) =
                typecheck_expression(sess, expr, fn_context, var_context)?;
            match typ {
                None => (),
                Some((((borrow_typ, _), (typ, _)), _)) => {
                    if (borrow_typ, &base_typ_to_computed(typ.clone()))
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
            let new_var_context = typecheck_pattern(
                sess,
                &(pat.clone(), pat_span.clone()),
                &(expr_typ_borrowing, expr_typ),
            )?;
            Ok((var_context.clone().union(new_var_context), HashSet::new()))
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
                    var_context.update(*x, (t_b.clone(), base_typ_to_computed(t.clone())))
                },
            );
            let out = Item::FnDecl(
                f,
                sig.clone(),
                (typecheck_block(sess, b, fn_context, &var_context)?, b_span),
            );
            let fn_context = fn_context.update(f, sig);
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
