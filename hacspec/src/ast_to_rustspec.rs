use im::HashSet;
use rustc_ast;
use rustc_ast::{
    ast::{
        self, AngleBracketedArg, Async, BindingMode, BlockCheckMode, BorrowKind, Const, Crate,
        Defaultness, Expr, ExprKind, Extern, FnRetTy, GenericArg, GenericArgs, IntTy, ItemKind,
        LitIntType, LitKind, MacArgs, MacCall, Mutability, Pat, PatKind, RangeLimits, Stmt,
        StmtKind, Ty, TyKind, UintTy, UnOp, Unsafe, UseTreeKind,
    },
    node_id::NodeId,
    token::{LitKind as TokenLitKind, TokenKind},
    tokenstream::TokenTree,
};
use rustc_session::Session;
use rustc_span::{symbol, Span};

use crate::rustspec::*;
use crate::RustspectErrorEmitter;

type ArrayTypes = HashSet<String>;

type TranslationResult<T> = Result<T, ()>;

fn check_vec<T>(v: Vec<TranslationResult<T>>) -> TranslationResult<Vec<T>> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn translate_ident(i: &symbol::Ident) -> Spanned<Ident> {
    (Ident::Original(i.name.to_ident_string()), i.span)
}

fn translate_type_args(
    sess: &Session,
    args: &GenericArgs,
    span: &Span,
) -> TranslationResult<Vec<Spanned<BaseTyp>>> {
    match args {
        GenericArgs::Parenthesized(_) => {
            sess.span_rustspec_err(
                *span,
                "parenthesized path arguments are not allowed in Rustspec",
            );
            Err(())
        }
        GenericArgs::AngleBracketed(args) => check_vec(
            args.args
                .iter()
                .map(|arg| match arg {
                    AngleBracketedArg::Constraint(_) => {
                        sess.span_rustspec_err(
                            args.span,
                            "contraint type arguments are not allowed in Rustspec",
                        );
                        Err(())
                    }
                    AngleBracketedArg::Arg(GenericArg::Type(ty)) => {
                        let typ_arg = translate_base_typ(sess, ty).map(|(t, _)| t);
                        Ok((typ_arg?, ty.span))
                    }
                    AngleBracketedArg::Arg(GenericArg::Lifetime(_)) => {
                        sess.span_rustspec_err(
                            args.span,
                            "lifetime type parameters are not allowed in Rustspect",
                        );
                        Err(())
                    }
                    AngleBracketedArg::Arg(GenericArg::Const(_)) => {
                        sess.span_rustspec_err(
                            args.span,
                            "const generics are not allowed in Rustspec",
                        );
                        Err(())
                    }
                })
                .collect(),
        ),
    }
}

pub fn translate_use_path(sess: &Session, path: &ast::Path) -> TranslationResult<String> {
    if path.segments.len() > 1 {
        sess.span_rustspec_err(path.span, "imports are limited to the top-level glob");
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty path are not allowed in Rustspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok(segment.ident.name.to_ident_string()),
            Some(_) => {
                sess.span_rustspec_err(path.span, "imports cannot have arguments");
                Err(())
            }
        },
    }
}

pub fn translate_typ_name(
    sess: &Session,
    path: &ast::Path,
) -> TranslationResult<(Spanned<Ident>, Option<Vec<Spanned<BaseTyp>>>)> {
    if path.segments.len() > 1 {
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty path are not allowed in Rustspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok((translate_ident(&segment.ident), None)),
            Some(generic_args) => Ok((
                translate_ident(&segment.ident),
                Some(translate_type_args(sess, generic_args, &path.span)?),
            )),
        },
    }
}

pub fn translate_expr_name(sess: &Session, path: &ast::Path) -> TranslationResult<Ident> {
    if path.segments.len() > 1 {
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty path are not allowed in Rustspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok(translate_ident(&segment.ident).0),
            Some(_) => {
                sess.span_rustspec_err(path.span, "expression paths cannot have arguments");
                Err(())
            }
        },
    }
}

pub fn translate_func_name(
    sess: &Session,
    path: &ast::Path,
) -> TranslationResult<(Option<Spanned<BaseTyp>>, Spanned<Ident>)> {
    if path.segments.len() > 2 {
        return Err(());
    }
    let prefix = if path.segments.len() == 2 {
        match path.segments.first() {
            None => panic!(), // should not happen
            Some(segment) => Some(translate_base_typ(
                sess,
                &ast::Ty {
                    span: path.span,
                    id: NodeId::MAX,
                    kind: TyKind::Path(
                        None,
                        ast::Path {
                            span: path.span,
                            segments: vec![segment.clone()],
                        },
                    ),
                },
            )?),
        }
    } else {
        None
    };
    Ok((
        prefix,
        translate_ident(&path.segments.last().unwrap().ident),
    ))
}

fn translate_base_typ(sess: &Session, ty: &Ty) -> TranslationResult<Spanned<BaseTyp>> {
    match &ty.kind {
        TyKind::Path(None, path) => {
            match &path.segments.as_slice() {
                [t] => match &t.args {
                    None => match t.ident.name.to_ident_string().as_str() {
                        "u32" => return Ok((BaseTyp::UInt32, ty.span)),
                        "i32" => return Ok((BaseTyp::Int32, ty.span)),
                        "u8" => return Ok((BaseTyp::UInt8, ty.span)),
                        "i8" => return Ok((BaseTyp::Int8, ty.span)),
                        "u16" => return Ok((BaseTyp::UInt16, ty.span)),
                        "i16" => return Ok((BaseTyp::Int16, ty.span)),
                        "u64" => return Ok((BaseTyp::UInt64, ty.span)),
                        "i64" => return Ok((BaseTyp::Int64, ty.span)),
                        "u128" => return Ok((BaseTyp::UInt128, ty.span)),
                        "i128" => return Ok((BaseTyp::Int128, ty.span)),
                        "bool" => return Ok((BaseTyp::Bool, ty.span)),
                        "usize" => return Ok((BaseTyp::Usize, ty.span)),
                        "isize" => return Ok((BaseTyp::Isize, ty.span)),
                        "Seq" => {
                            sess.span_rustspec_err(ty.span, "Seq expects a type argument");
                            return Err(());
                        }
                        _ => (),
                    },
                    Some(args) => match t.ident.name.to_ident_string().as_str() {
                        "Seq" => {
                            let args = translate_type_args(sess, args, &path.span)?;
                            if args.len() > 1 {
                                sess.span_rustspec_err(
                                    ty.span.clone(),
                                    "Seq cannot have multiple type arguments",
                                );
                                return Err(());
                            }
                            return Ok((
                                BaseTyp::Seq(Box::new(args.first().unwrap().clone())),
                                path.span,
                            ));
                        }
                        _ => (),
                    },
                },
                _ => (),
            };
            let (name, arg) = translate_typ_name(sess, path)?;
            Ok((BaseTyp::Named(name, arg), ty.span))
        }
        TyKind::Tup(tys) => {
            let rtys: Vec<TranslationResult<Spanned<BaseTyp>>> = tys
                .into_iter()
                .map(|ty| translate_base_typ(sess, ty))
                .collect();
            let rtys = check_vec(rtys)?;
            Ok((BaseTyp::Tuple(rtys), ty.span))
        }
        TyKind::Path(Some(_), _) => {
            sess.span_rustspec_err(ty.span, "trait associated types not allowed in Rustspec");
            Err(())
        }
        TyKind::Rptr(_, _) => {
            sess.span_rustspec_err(ty.span, "double references not allowed in Rustspec");
            Err(())
        }
        _ => {
            sess.span_rustspec_err(ty.span, "type not allowed in Rustspec");
            Err(())
        }
    }
}

fn translate_typ(sess: &Session, ty: &Ty) -> TranslationResult<Spanned<Typ>> {
    match &ty.kind {
        TyKind::Rptr(None, mut_ty) => match &mut_ty.mutbl {
            Mutability::Mut => {
                sess.span_rustspec_err(ty.span, "mutable function arguments are not allowed");
                Err(())
            }
            Mutability::Not => translate_base_typ(sess, &mut_ty.ty)
                .map(|t| (((Borrowing::Borrowed, ty.span), t), ty.span)),
        },
        TyKind::Rptr(Some(_), _) => {
            sess.span_rustspec_err(ty.span, "lifetime annotations are not allowed in Rustspec");
            Err(())
        }
        _ => translate_base_typ(sess, ty).map(|t| (((Borrowing::Consumed, ty.span), t), ty.span)),
    }
}

enum ExprTranslationResult {
    TransExpr(Expression),
    TransStmt(Statement),
}

fn translate_expr_expects_exp(
    sess: &Session,
    arr_typs: &ArrayTypes,
    e: &Expr,
) -> TranslationResult<Spanned<Expression>> {
    match translate_expr(sess, arr_typs, e)? {
        (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
        (ExprTranslationResult::TransStmt(_), span) => {
            sess.span_rustspec_err(
                span,
                "statements inside expressions are not allowed in Rustspec",
            );
            Err(())
        }
    }
}

fn translate_function_argument(
    sess: &Session,
    arr_typs: &ArrayTypes,
    e: &Expr,
) -> TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)> {
    match &e.kind {
        ExprKind::AddrOf(BorrowKind::Ref, is_mut, e1) => match is_mut {
            Mutability::Mut => {
                sess.span_rustspec_err(e.span, "mutable borrows are forbidden in Rustspec");
                Err(())
            }
            Mutability::Not => Ok((
                translate_expr_expects_exp(sess, arr_typs, e1)?,
                (Borrowing::Borrowed, e.span.clone()),
            )),
        },
        _ => Ok((
            translate_expr_expects_exp(sess, arr_typs, e)?,
            (Borrowing::Consumed, e.span.clone()),
        )),
    }
}

fn translate_expr(
    sess: &Session,
    arr_typs: &ArrayTypes,
    e: &Expr,
) -> TranslationResult<Spanned<ExprTranslationResult>> {
    match &e.kind {
        ExprKind::Binary(op, e1, e2) => Ok((
            ExprTranslationResult::TransExpr(Expression::Binary(
                (op.clone().node, op.clone().span),
                Box::new(translate_expr_expects_exp(sess, arr_typs, e1)?),
                Box::new(translate_expr_expects_exp(sess, arr_typs, e2)?),
            )),
            e.span,
        )),
        ExprKind::Unary(op, e1) => Ok((
            ExprTranslationResult::TransExpr(Expression::Unary(
                match *op {
                    UnOp::Not => UnOpKind::Not,
                    UnOp::Neg => UnOpKind::Neg,
                    UnOp::Deref => {
                        sess.span_rustspec_err(e.span, "dereferences not allowed in Rustspec");
                        return Err(());
                    }
                },
                Box::new(translate_expr_expects_exp(sess, arr_typs, e1)?),
            )),
            e.span,
        )),
        ExprKind::Path(Some(_), _) => {
            sess.span_rustspec_err(e.span, "trait associated values not allowed in Rustspec");
            Err(())
        }
        ExprKind::Path(None, path) => Ok((
            ExprTranslationResult::TransExpr(Expression::Named(translate_expr_name(sess, path)?)),
            e.span,
        )),
        ExprKind::Call(func, args) => {
            let ((func_prefix, func_name), _) = match &func.kind {
                ExprKind::Path(None, path) => Ok((translate_func_name(sess, &path)?, path.span)),
                _ => {
                    sess.span_rustspec_err(
                        func.span,
                        "function expressions are restricted to names only in Rustspec",
                    );
                    Err(())
                }
            }?;
            let func_name_string = match func_name.0 {
                Ident::Original(ref s) => s,
                _ => panic!(), // should not happen}
            };
            if arr_typs.contains(func_name_string) {
                // Special case for array constructors
                if args.len() != 1 {
                    sess.span_rustspec_err(
                        e.span,
                        "array constructor called with more than one arguments",
                    );
                    return Err(());
                }
                match &args.first().unwrap().kind {
                    ExprKind::Array(cells) => {
                        let new_cells: Vec<TranslationResult<Spanned<Expression>>> = cells
                            .iter()
                            .map(|cell| translate_expr_expects_exp(sess, arr_typs, &cell))
                            .collect();
                        let new_cells = check_vec(new_cells)?;
                        return Ok((
                            (ExprTranslationResult::TransExpr(Expression::NewArray(
                                func_name, None, new_cells,
                            ))),
                            e.span,
                        ));
                    }
                    _ => {
                        sess.span_rustspec_err(
                            args.first().unwrap().span.clone(),
                            "expected an array literal",
                        );
                        return Err(());
                    }
                }
            }
            let func_args: Vec<TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)>> = args
                .iter()
                .map(|arg| translate_function_argument(sess, arr_typs, &arg))
                .collect();
            let func_args = check_vec(func_args);
            Ok((
                ExprTranslationResult::TransExpr(Expression::FuncCall(
                    func_prefix,
                    func_name,
                    func_args?,
                )),
                e.span,
            ))
        }
        ExprKind::MethodCall(method_name, args, span) => {
            let func_args: Vec<TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)>> = args
                .iter()
                .map(|arg| translate_function_argument(sess, arr_typs, &arg))
                .collect();
            let func_args = check_vec(func_args)?;
            let (method_arg, rest_args) = func_args.split_at(1);
            let method_arg = method_arg
                .first()
                .map_or(Err(()), |x| Ok(Box::new(x.clone())))?;
            let method_name = match method_name.args {
                None => Ok(translate_ident(&method_name.ident)),
                Some(_) => {
                    sess.span_rustspec_err(*span, "method type arguments not allowed in Rustspec");
                    Err(())
                }
            }?;
            let mut rest_args_final = Vec::new();
            rest_args_final.extend_from_slice(rest_args);
            Ok((
                ExprTranslationResult::TransExpr(Expression::MethodCall(
                    method_arg,
                    None,
                    method_name,
                    rest_args_final,
                )),
                e.span,
            ))
        }
        ExprKind::Lit(lit) => match &lit.kind {
            LitKind::Bool(b) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Bool(*b))),
                e.span,
            )),
            //TODO: check that the casting is safe each time!
            LitKind::Int(x, LitIntType::Signed(IntTy::I128)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int128(*x as i128))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::U128)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt128(*x as u128))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::I64)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int64(*x as i64))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::U64)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt64(*x as u64))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::I32)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int32(*x as i32))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::U32)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt32(*x as u32))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::I16)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int16(*x as i16))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::U16)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt16(*x as u16))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::I8)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int8(*x as i8))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::U8)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt8(*x as u8))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::Isize)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Isize(*x as isize))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsigned(UintTy::Usize)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Usize(*x as usize))),
                e.span,
            )),
            // Unspecified integers are always interpreted as usize
            LitKind::Int(x, LitIntType::Unsuffixed) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Usize(*x as usize))),
                e.span,
            )),
            _ => {
                sess.span_rustspec_err(lit.span, "literal not allowed in Rustspec");
                Err(())
            }
        },
        ExprKind::Assign(lhs, rhs_e, _) => {
            let r_e = translate_expr(sess, arr_typs, rhs_e)?;
            match &lhs.kind {
                ExprKind::Path(None, path) => match &path.segments.as_slice() {
                    [var] => match &var.args {
                        None => {
                            let id = translate_ident(&var.ident);

                            match r_e {
                                (ExprTranslationResult::TransStmt(_), span) => {
                                    sess.span_rustspec_err(span, "statements not allowed in Rustspec for assignments right-hand-sides");
                                    Err(())
                                }
                                (ExprTranslationResult::TransExpr(r_e), span) => Ok((
                                    ExprTranslationResult::TransStmt(Statement::Reassignment(
                                        id,
                                        (r_e, span),
                                    )),
                                    e.span,
                                )),
                            }
                        }
                        Some(_) => {
                            sess.span_rustspec_err(path.span, "no arguments expected in Rustspec");
                            Err(())
                        }
                    },
                    _ => {
                        sess.span_rustspec_err(
                            path.span,
                            "wrong assignment left-hand-side variable",
                        );
                        Err(())
                    }
                },
                ExprKind::Index(a, index) => {
                    let r_index = translate_expr(sess, arr_typs, index)?;
                    let r_index = match r_index {
                        (ExprTranslationResult::TransStmt(_), span) => {
                            sess.span_rustspec_err(span, "statements not allowed in Rustspec for assignments left-hand-sides");
                            Err(())
                        }
                        (ExprTranslationResult::TransExpr(r_index), span) => Ok((r_index, span)),
                    };
                    match &a.kind {
                        ExprKind::Path(None, path) => match path.segments.as_slice() {
                            [var] => match &var.args {
                                None => {
                                    let id = translate_ident(&var.ident);
                                    match r_e {
                                        (ExprTranslationResult::TransStmt(_), span) => {
                                            sess.span_rustspec_err(span, "statements not allowed in Rustspec for assignments right-hand-sides");
                                            Err(())
                                        }
                                        (ExprTranslationResult::TransExpr(r_e), span) => Ok((
                                            ExprTranslationResult::TransStmt(
                                                Statement::ArrayUpdate(id, r_index?, (r_e, span)),
                                            ),
                                            e.span,
                                        )),
                                    }
                                }
                                Some(_) => {
                                    sess.span_rustspec_err(
                                        path.span,
                                        "no arguments expected in Rustspec",
                                    );
                                    Err(())
                                }
                            },
                            _ => {
                                sess.span_rustspec_err(
                                    path.span,
                                    "wrong assignment left-hand-side array update variable",
                                );
                                Err(())
                            }
                        },
                        _ => {
                            sess.span_rustspec_err(a.span, "Rustspect only allows array updates on arrays that are explicitely let-binded in a variable");
                            Err(())
                        }
                    }
                }
                _ => {
                    sess.span_rustspec_err(
                        lhs.span,
                        "left-hand side of the assignment must be variables in Rustspec",
                    );
                    Err(())
                }
            }
        }
        ExprKind::If(cond, t_e, f_e) => {
            let r_cond = match translate_expr(sess, arr_typs, cond)? {
                (ExprTranslationResult::TransStmt(_), span) => {
                    sess.span_rustspec_err(
                        span,
                        "statements not allowed inside conditions in Rustspec",
                    );
                    Err(())
                }
                (ExprTranslationResult::TransExpr(r_cond), span) => Ok((r_cond, span)),
            };
            let r_t_e = translate_block(sess, arr_typs, t_e)?;
            let r_f_e: TranslationResult<Option<Spanned<Block>>> = match f_e {
                None => Ok(None),
                Some(f_e) => match &f_e.kind {
                    ExprKind::Block(f_e, _) => {
                        let r_f_e = translate_block(sess, arr_typs, f_e)?;
                        Ok(Some(r_f_e))
                    }
                    _ => {
                        sess.span_rustspec_err(
                            f_e.span,
                            "block of statements expected in the else branch in Rustspec",
                        );
                        Err(())
                    }
                },
            };
            Ok((
                ExprTranslationResult::TransStmt(Statement::Conditional(
                    r_cond?, r_t_e, r_f_e?, None,
                )),
                e.span,
            ))
        }
        ExprKind::ForLoop(pat, range, b, _) => {
            let id = match &pat.kind {
                PatKind::Ident(BindingMode::ByValue(Mutability::Not), id, None) => {
                    Ok(translate_ident(id))
                }
                _ => {
                    sess.span_rustspec_err(
                        pat.span,
                        "only single-variable-binding patterns are allowed for loops in Rustspec",
                    );
                    Err(())
                }
            };
            let e_begin_end = match &range.kind {
                ExprKind::Range(Some(r_begin), Some(r_end), RangeLimits::HalfOpen) => {
                    let e_begin = translate_expr(sess, arr_typs, r_begin)?;
                    let e_end = translate_expr(sess, arr_typs, r_end)?;
                    match (e_begin, e_end) {
                        (
                            (ExprTranslationResult::TransExpr(e_begin), span_begin),
                            (ExprTranslationResult::TransExpr(e_end), span_end),
                        ) => Ok(((e_begin, span_begin), (e_end, span_end))),
                        _ => {
                            sess.span_rustspec_err(
                                range.span,
                                "range expressions cannot contain statements in Rustspec",
                            );
                            Err(())
                        }
                    }
                }
                _ => {
                    sess.span_rustspec_err(
                        range.span,
                        "expected a non-inclusive range expression here in Rustspec",
                    );
                    Err(())
                }
            };
            let (e_begin, e_end) = e_begin_end?;
            let r_b = translate_block(sess, arr_typs, b)?;
            Ok((
                ExprTranslationResult::TransStmt(Statement::ForLoop(id?, e_begin, e_end, r_b)),
                e.span,
            ))
        }
        ExprKind::Index(a, e2) => match &a.kind {
            ExprKind::Path(None, path) => match path.segments.as_slice() {
                [var] => match &var.args {
                    None => {
                        let id = translate_ident(&var.ident);
                        let r_e2 = translate_expr(sess, arr_typs, e2)?;
                        match r_e2 {
                            (ExprTranslationResult::TransExpr(r_e2), r_e2_span) => Ok((
                                ExprTranslationResult::TransExpr(Expression::ArrayIndex(
                                    id,
                                    Box::new((r_e2, r_e2_span)),
                                )),
                                e.span,
                            )),
                            _ => {
                                sess.span_rustspec_err(
                                        e.span,
                                        "statements not allowed in Rustspec inside array indexing expression",
                                    );
                                Err(())
                            }
                        }
                    }
                    Some(_) => {
                        sess.span_rustspec_err(path.span, "no arguments expected in Rustspec");
                        Err(())
                    }
                },
                _ => {
                    sess.span_rustspec_err(path.span, "can only index local arrays");
                    Err(())
                }
            },
            _ => {
                sess.span_rustspec_err(a.span, "Rustspect only allows array indexing on arrays that are explicitely let-binded in a variable");
                Err(())
            }
        },
        ExprKind::Tup(args) => {
            let r_args = args
                .into_iter()
                .map(|arg| match translate_expr(sess, arr_typs, arg)? {
                    (ExprTranslationResult::TransExpr(r_arg), r_span) => Ok((r_arg, r_span)),
                    (ExprTranslationResult::TransStmt(_), r_span) => {
                        sess.span_rustspec_err(
                            r_span,
                            "statements forbidden in tuple expressions in Rustspec",
                        );
                        Err(())
                    }
                })
                .collect();
            let r_args = check_vec(r_args)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::Tuple(r_args)),
                e.span,
            ))
        }
        ExprKind::Struct(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO1");
            Err(())
        }
        ExprKind::Box(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO2");
            Err(())
        }
        ExprKind::Array(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO3");
            Err(())
        }
        ExprKind::Cast(e1, t1) => {
            let new_e1 = translate_expr_expects_exp(sess, arr_typs, e1)?;
            let new_t1 = translate_base_typ(sess, t1)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::IntegerCasting(
                    Box::new(new_e1),
                    new_t1,
                )),
                e.span.clone(),
            ))
        }
        ExprKind::Type(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO5");
            Err(())
        }
        ExprKind::Let(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO5");
            Err(())
        }
        ExprKind::While(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO6");
            Err(())
        }
        ExprKind::Loop(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO7");
            Err(())
        }
        ExprKind::Match(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO8");
            Err(())
        }
        ExprKind::Closure(_, _, _, _, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO9");
            Err(())
        }
        ExprKind::Block(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO10");
            Err(())
        }
        ExprKind::Async(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO11");
            Err(())
        }
        ExprKind::Await(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO12");
            Err(())
        }
        ExprKind::TryBlock(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO13");
            Err(())
        }
        ExprKind::AssignOp(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO14");
            Err(())
        }
        ExprKind::Field(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO15");
            Err(())
        }
        ExprKind::Range(e1, e2, limits) => {
            match limits {
                RangeLimits::HalfOpen => (),
                RangeLimits::Closed => {
                    sess.span_rustspec_err(e.span, "inclusive ranges not allowed");
                    return Err(());
                }
            }
            let e1 = match e1 {
                Some(e1) => e1,
                None => {
                    sess.span_rustspec_err(e.span, "missing left bound of the range");
                    return Err(());
                }
            };
            let e2 = match e2 {
                Some(e2) => e2,
                None => {
                    sess.span_rustspec_err(e.span, "missing right bound of the range");
                    return Err(());
                }
            };
            let new_e1 = translate_expr_expects_exp(sess, arr_typs, e1)?;
            let new_e2 = translate_expr_expects_exp(sess, arr_typs, e2)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::Tuple(vec![new_e1, new_e2])),
                e.span,
            ))
        }
        ExprKind::AddrOf(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO17");
            Err(())
        }
        ExprKind::Break(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO18");
            Err(())
        }
        ExprKind::Continue(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO19");
            Err(())
        }
        ExprKind::Ret(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO20");
            Err(())
        }
        ExprKind::InlineAsm(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO21");
            Err(())
        }
        ExprKind::LlvmInlineAsm(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO22");
            Err(())
        }
        ExprKind::MacCall(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO23");
            Err(())
        }
        ExprKind::Repeat(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "FOO24");
            Err(())
        }
        ExprKind::Yield(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO25");
            Err(())
        }
        ExprKind::Paren(e1) => translate_expr(sess, arr_typs, e1),
        ExprKind::Try(_) => {
            sess.span_rustspec_err(e.span.clone(), "FOO27");
            Err(())
        }
        _ => {
            sess.span_rustspec_err(e.span, "this expression is not allowed in Rustspec");
            Err(())
        }
    }
}

fn translate_pattern(sess: &Session, pat: &Pat) -> TranslationResult<Spanned<Pattern>> {
    match &pat.kind {
        PatKind::Ident(BindingMode::ByValue(_), id, None) => {
            Ok((Pattern::IdentPat(translate_ident(id).0), pat.span))
        }
        PatKind::Tuple(pats) => {
            let pats = pats
                .into_iter()
                .map(|pat| translate_pattern(sess, pat))
                .collect();
            let pats = check_vec(pats)?;
            Ok((Pattern::Tuple(pats), pat.span))
        }
        PatKind::Wild => Ok((Pattern::WildCard, pat.span)),
        _ => {
            sess.span_rustspec_err(pat.span, "pattern not allowed in Rustspec let bindings");
            Err(())
        }
    }
}

fn translate_statement(
    sess: &Session,
    arr_typs: &ArrayTypes,
    s: &Stmt,
) -> TranslationResult<Vec<Spanned<Statement>>> {
    match &s.kind {
        StmtKind::Item(_) => {
            sess.span_rustspec_err(s.span, "block-local items are not allowed in Rustspec");
            Err(())
        }
        StmtKind::MacCall(_) => {
            sess.span_rustspec_err(
                s.span,
                "macro calls inside code blocks are not allowed inside Rustspec",
            );
            Err(())
        }
        StmtKind::Empty => {
            sess.span_rustspec_err(s.span, "empty blocks are not allowed in Rustspec");
            Err(())
        }
        StmtKind::Local(local) => {
            let pat = translate_pattern(sess, &local.pat)?;
            let ty: Option<Spanned<Typ>> = match local.ty.clone() {
                None => None,
                Some(ty) => Some(translate_typ(sess, &ty)?),
            };
            let init = match &local.init {
                None => {
                    sess.span_rustspec_err(
                        local.span,
                        "let-bindings without initialization are not allowed in Rustspec",
                    );
                    Err(())
                }
                Some(e) => match translate_expr(sess, arr_typs, &e)? {
                    (ExprTranslationResult::TransStmt(_), _) => {
                        sess.span_rustspec_err(
                            e.span,
                            "let binding expression should not contain statements in Rustspec",
                        );
                        Err(())
                    }
                    (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
                },
            }?;
            Ok(vec![(Statement::LetBinding(pat, ty, init), s.span)])
        }
        StmtKind::Expr(e) => {
            let t_s = match translate_expr(sess, arr_typs, &e)? {
                (ExprTranslationResult::TransExpr(e), _) => Statement::ReturnExp(e),
                (ExprTranslationResult::TransStmt(s), _) => s,
            };
            Ok(vec![(t_s, s.span)])
        }
        StmtKind::Semi(e) => {
            let t_s = match translate_expr(sess, arr_typs, &e)? {
                (ExprTranslationResult::TransExpr(e), span) => {
                    Statement::LetBinding((Pattern::WildCard, span), None, (e, span))
                }
                (ExprTranslationResult::TransStmt(s), _) => s,
            };
            Ok(vec![(t_s, s.span)])
        }
    }
}

fn translate_block(
    sess: &Session,
    arr_typs: &ArrayTypes,
    b: &ast::Block,
) -> TranslationResult<Spanned<Block>> {
    match b.rules {
        BlockCheckMode::Unsafe(_) => {
            sess.span_rustspec_err(b.span, "unsafe blocks are not allowed in Rustspec");
            return Err(());
        }
        BlockCheckMode::Default => (),
    };
    let stmts = b
        .stmts
        .iter()
        .map(|s| translate_statement(sess, arr_typs, &s))
        .collect();
    let stmts = check_vec(stmts)?.into_iter().flatten().collect();
    Ok((
        Block {
            stmts,
            return_typ: None,
            mutated: None,
            // We initialize these fields to None as they are
            // to be filled by the typechecker
        },
        b.span,
    ))
}

enum ItemTranslationResult {
    Item(Item),
    ImportedCrate(String),
}

fn check_for_comma(sess: &Session, arg: &TokenTree) -> TranslationResult<()> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Comma => Ok(()),
            _ => {
                sess.span_rustspec_err(tok.span.clone(), "expected a comma");
                Err(())
            }
        },
        _ => {
            sess.span_rustspec_err(
                arg.span().clone(),
                "expected delimiter to be a single token",
            );
            Err(())
        }
    }
}

fn check_for_usize(sess: &Session, arg: &TokenTree) -> TranslationResult<Spanned<Expression>> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Literal(lit) => match lit.kind {
                TokenLitKind::Integer => match lit.suffix {
                    Some(_) => {
                        sess.span_rustspec_err(
                            tok.span.clone(),
                            "no suffix expected for size specification literal",
                        );
                        Err(())
                    }
                    None => match lit.symbol.to_ident_string().parse::<usize>() {
                        Err(_) => {
                            sess.span_rustspec_err(
                                tok.span.clone(),
                                "unable to parse integer into an usize",
                            );
                            Err(())
                        }
                        Ok(x) => Ok((Expression::Lit(Literal::Usize(x)), tok.span.clone())),
                    },
                },
                _ => {
                    sess.span_rustspec_err(tok.span.clone(), "expected an integer");
                    Err(())
                }
            },
            TokenKind::Ident(name, _) => Ok((
                Expression::Named(Ident::Original(name.to_ident_string())),
                tok.span.clone(),
            )),
            _ => {
                sess.span_rustspec_err(tok.span.clone(), "expected a literal");
                Err(())
            }
        },
        _ => {
            sess.span_rustspec_err(arg.span().clone(), "expected argument to be a single token");
            Err(())
        }
    }
}

fn check_for_ident(sess: &Session, arg: &TokenTree) -> TranslationResult<(Spanned<Ident>, String)> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Ident(id, _) => Ok((
                (Ident::Original(id.to_ident_string()), tok.span.clone()),
                id.to_ident_string(),
            )),
            _ => {
                sess.span_rustspec_err(tok.span.clone(), "expected an identifier");
                Err(())
            }
        },
        _ => {
            sess.span_rustspec_err(arg.span().clone(), "expected argument to be a single token");
            Err(())
        }
    }
}

fn translate_natural_integer_decl(
    sess: &Session,
    i: &ast::Item,
    arr_types: &ArrayTypes,
    call: &MacCall,
    secrecy: Secrecy,
) -> TranslationResult<(ItemTranslationResult, ArrayTypes)> {
    match &*call.args {
        MacArgs::Delimited(_, _, tokens) => {
            let mut it = tokens.trees();
            let (first_arg, second_arg, third_arg, fourth_arg, fifth_arg, sixth_arg, seventh_arg) =
                {
                    let first_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let second_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let third_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let fourth_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let fifth_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let sixth_arg = it.next().map_or(Err(()), |x| Ok(x));
                    let seventh_arg = it.next().map_or(Err(()), |x| Ok(x));
                    Ok((
                        first_arg?,
                        second_arg?,
                        third_arg?,
                        fourth_arg?,
                        fifth_arg?,
                        sixth_arg?,
                        seventh_arg?,
                    ))
                }?;
            let (typ_ident, typ_ident_string) = check_for_ident(sess, &first_arg)?;
            check_for_comma(sess, &second_arg)?;
            let (canvas_typ_ident, _) = check_for_ident(sess, &third_arg)?;
            check_for_comma(sess, &fourth_arg)?;
            let canvas_size = check_for_usize(sess, &fifth_arg)?;
            check_for_comma(sess, &sixth_arg)?;
            let modulo_string = match &seventh_arg {
                TokenTree::Token(tok) => match tok.kind {
                    TokenKind::Literal(lit) => match lit.kind {
                        TokenLitKind::Str => {
                            (lit.symbol.to_ident_string(), seventh_arg.span().clone())
                        }
                        _ => {
                            sess.span_rustspec_err(tok.span.clone(), "expected a  string literal");
                            return Err(());
                        }
                    },
                    _ => {
                        sess.span_rustspec_err(tok.span.clone(), "expected a literal");
                        return Err(());
                    }
                },
                _ => {
                    sess.span_rustspec_err(
                        seventh_arg.span().clone(),
                        "expected argument to be a single token",
                    );
                    return Err(());
                }
            };
            Ok((
                (ItemTranslationResult::Item(Item::NaturalIntegerDecl(
                    typ_ident,
                    canvas_typ_ident,
                    secrecy,
                    canvas_size,
                    modulo_string,
                ))),
                arr_types.update(typ_ident_string),
            ))
        }
        _ => {
            sess.span_rustspec_err(i.span.clone(), "expected delimited macro arguments");
            Err(())
        }
    }
}

fn translate_array_decl(
    sess: &Session,
    i: &ast::Item,
    arr_types: &ArrayTypes,
    call: &MacCall,
    cell_t: Option<BaseTyp>,
) -> TranslationResult<(ItemTranslationResult, ArrayTypes)> {
    match &*call.args {
        MacArgs::Delimited(_, _, tokens) => {
            let mut it = tokens.trees();
            let (first_arg, second_arg, third_arg) = {
                let first_arg = it.next().map_or(Err(()), |x| Ok(x));
                let second_arg = it.next().map_or(Err(()), |x| Ok(x));
                let third_arg = it.next().map_or(Err(()), |x| Ok(x));
                Ok((first_arg?, second_arg?, third_arg?))
            }?;
            let (typ_ident, typ_ident_string) = check_for_ident(sess, &first_arg)?;
            check_for_comma(sess, &second_arg)?;
            let size = check_for_usize(sess, &third_arg)?;
            let cell_t = match cell_t {
                None => {
                    let (fourth_arg, fifth_arg) = {
                        let fourth_arg = it.next().map_or(Err(()), |x| Ok(x));
                        let fifth_arg = it.next().map_or(Err(()), |x| Ok(x));
                        Ok((fourth_arg?, fifth_arg?))
                    }?;
                    check_for_comma(sess, &fourth_arg)?;
                    let cell_t = match fifth_arg {
                        TokenTree::Token(tok) => match tok.kind {
                            TokenKind::Ident(id, _) => translate_base_typ(
                                sess,
                                &Ty {
                                    id: NodeId::MAX,
                                    kind: TyKind::Path(
                                        None,
                                        ast::Path::from_ident(symbol::Ident {
                                            name: id,
                                            span: tok.span.clone(),
                                        }),
                                    ),
                                    span: tok.span.clone(),
                                },
                            ),
                            _ => {
                                sess.span_rustspec_err(tok.span.clone(), "expected an identifier");
                                return Err(());
                            }
                        },
                        _ => {
                            sess.span_rustspec_err(
                                i.span.clone(),
                                "expected first argument to be a single token",
                            );
                            return Err(());
                        }
                    }?;
                    cell_t
                }
                Some(t) => (t, typ_ident.1.clone()),
            };
            Ok((
                (ItemTranslationResult::Item(Item::ArrayDecl(typ_ident, size, cell_t))),
                arr_types.update(typ_ident_string),
            ))
        }
        _ => {
            sess.span_rustspec_err(i.span.clone(), "expected delimited macro arguments");
            Err(())
        }
    }
}

fn translate_items(
    sess: &Session,
    i: &ast::Item,
    arr_types: &ArrayTypes,
) -> TranslationResult<(ItemTranslationResult, ArrayTypes)> {
    match &i.kind {
        ItemKind::Fn(defaultness, ref sig, ref generics, ref body) => {
            // First, checking that no fancy function qualifier is here
            match defaultness {
                Defaultness::Default(span) => {
                    sess.span_rustspec_err(
                        span.clone(),
                        "\"default\" keyword not allowed in Rustspec",
                    );
                    return Err(());
                }
                _ => (),
            }
            match sig.header.unsafety {
                Unsafe::No => (),
                Unsafe::Yes(span) => {
                    sess.span_rustspec_err(
                        span.clone(),
                        "unsafe functions not allowed in Rustspec",
                    );
                    return Err(());
                }
            }
            match sig.header.asyncness {
                Async::No => (),
                Async::Yes { span, .. } => {
                    sess.span_rustspec_err(span.clone(), "async functions not allowed in Rustspec");
                    return Err(());
                }
            }
            match sig.header.constness {
                Const::No => (),
                Const::Yes(span) => {
                    sess.span_rustspec_err(span.clone(), "const functions not allowed in Rustspec");
                    return Err(());
                }
            }
            match sig.header.ext {
                Extern::None => (),
                _ => {
                    sess.span_rustspec_err(
                        i.span.clone(),
                        "extern functions not allowed in Rustspec",
                    );
                    return Err(());
                }
            }
            // Then, translating the signature
            let fn_inputs: Vec<TranslationResult<(Spanned<Ident>, Spanned<Typ>)>> = sig
                .decl
                .inputs
                .iter()
                .map(|param| {
                    // For now, we don't allow pattern destructuring in functions signatures
                    let id = match param.pat.kind {
                        PatKind::Ident(BindingMode::ByValue(Mutability::Not), id, None) => {
                            Ok(translate_ident(&id))
                        }
                        PatKind::Wild => {
                            sess.span_rustspec_err(
                                param.pat.span.clone(),
                                "please give a name to this function argument",
                            );
                            Err(())
                        }
                        _ => {
                            sess.span_rustspec_err(
                            param.pat.span.clone(),
                            "pattern destructuring in function arguments not allowed in Rustspec",
                        );
                            Err(())
                        }
                    };
                    let ty = translate_typ(sess, &param.ty);
                    match (id, ty) {
                        (Ok(id), Ok(ty)) => Ok((id, ty)),
                        _ => Err(()),
                    }
                })
                .collect();
            if generics.params.len() != 0 {
                sess.span_rustspec_err(
                    generics.span.clone(),
                    "generics are not allowed in Rustspec",
                );
                return Err(());
            };
            let fn_inputs = check_vec(fn_inputs)?;
            let fn_output = match &sig.decl.output {
                FnRetTy::Default(span) => (BaseTyp::Unit, span.clone()),
                FnRetTy::Ty(ty) => translate_base_typ(sess, ty)?,
            };
            let fn_body: Spanned<Block> = match body {
                None => (
                    Block {
                        stmts: Vec::new(),
                        return_typ: None,
                        mutated: None,
                    },
                    i.span,
                ),
                Some(b) => translate_block(sess, arr_types, &b)?,
            };
            let fn_sig = FuncSig {
                args: fn_inputs,
                ret: fn_output,
            };
            Ok((
                ItemTranslationResult::Item(Item::FnDecl(
                    translate_ident(&i.ident),
                    fn_sig,
                    fn_body,
                )),
                arr_types.clone(),
            ))
        }
        ItemKind::Use(ref tree) => match tree.kind {
            // TODO: better system
            UseTreeKind::Glob => Ok((
                ItemTranslationResult::ImportedCrate(translate_use_path(sess, &tree.prefix)?),
                arr_types.clone(),
            )),
            _ => {
                sess.span_rustspec_err(tree.span.clone(), "only ::* uses are allowed in Rustspec");
                Err(())
            }
        },
        ItemKind::MacCall(call) => {
            if call.path.segments.len() > 1 {
                sess.span_rustspec_err(
                    call.path.span,
                    "cannot use macros other than the ones defined by Rustspec",
                );
                return Err(());
            }
            let name = call.path.segments.first().unwrap();
            match (
                name.ident.name.to_ident_string().as_str(),
                name.args.as_ref(),
            ) {
                ("array", None) => translate_array_decl(sess, i, arr_types, call, None),
                ("bytes", None) => translate_array_decl(
                    sess,
                    i,
                    arr_types,
                    call,
                    Some(BaseTyp::Named(
                        (Ident::Original("U8".into()), i.span.clone()),
                        None,
                    )),
                ),
                ("public_bytes", None) => {
                    translate_array_decl(sess, i, arr_types, call, Some(BaseTyp::UInt8))
                }
                ("public_nat_mod", None) => {
                    translate_natural_integer_decl(sess, i, arr_types, call, Secrecy::Public)
                }
                ("nat_mod", None) => {
                    translate_natural_integer_decl(sess, i, arr_types, call, Secrecy::Secret)
                }
                (_, None) => {
                    sess.span_rustspec_err(name.ident.span.clone(), "unknown Rustspec macro");
                    Err(())
                }
                (_, Some(_)) => {
                    sess.span_rustspec_err(
                        name.ident.span.clone(),
                        "macro names should not have arguments",
                    );
                    Err(())
                }
            }
        }
        ItemKind::Const(_, ty, Some(e)) => {
            let new_ty = translate_base_typ(sess, ty)?;
            let new_e = translate_expr_expects_exp(sess, arr_types, e)?;
            let id = translate_ident(&i.ident);
            Ok((
                ItemTranslationResult::Item(Item::ConstDecl(id, new_ty, new_e)),
                arr_types.clone(),
            ))
        }
        _ => {
            sess.span_rustspec_err(i.span.clone(), "item not allowed in Rustspec");
            Err(())
        }
    }
}

pub fn translate(sess: &Session, krate: &Crate) -> TranslationResult<Program> {
    let items = &krate.module.items;
    let mut arr_types = HashSet::new();
    let translated_items = check_vec(
        items
            .into_iter()
            .map(|i| {
                let (new_i, new_arr_typs) = translate_items(sess, &i, &arr_types)?;
                arr_types = new_arr_typs;
                Ok((new_i, i.span))
            })
            .collect(),
    )?;
    let (items, imports): (Vec<_>, Vec<_>) =
        translated_items.into_iter().partition(|(r, _)| match r {
            ItemTranslationResult::Item(_) => true,
            ItemTranslationResult::ImportedCrate(_) => false,
        });
    let items = items
        .into_iter()
        .map(|(r, r_span)| {
            match r {
                ItemTranslationResult::Item(i) => (i, r_span),
                _ => panic!(), // should not happen
            }
        })
        .collect();
    let imports = imports
        .into_iter()
        .map(|(r, r_span)| {
            match r {
                ItemTranslationResult::ImportedCrate(i) => (i, r_span),
                _ => panic!(), // should not happen
            }
        })
        .collect();
    Ok(Program {
        items,
        imported_crates: imports,
    })
}
