use rustc_ast;
use rustc_ast::ast::{
    self, AngleBracketedArg, Async, BindingMode, BlockCheckMode, Const, Crate, Defaultness, Expr,
    ExprKind, Extern, FnRetTy, GenericArg, GenericArgs, IntTy, ItemKind, LitIntType, LitKind,
    Mutability, PatKind, Stmt, StmtKind, Ty, TyKind, Unsafe,
};
use rustc_session::Session;
use rustc_span::{symbol::Ident, Span};

use crate::rustspec::*;

type TranslationResult<T> = Result<T, ()>;

fn check_vec<T>(v: Vec<TranslationResult<T>>) -> TranslationResult<Vec<T>> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn translate_type_arg(
    sess: &Session,
    args: &GenericArgs,
    span: &Span,
) -> TranslationResult<Spanned<BaseTyp>> {
    match args {
        GenericArgs::Parenthesized(_) => {
            sess.span_err(
                *span,
                "parenthesized path arguments are not allowed in Rustspec",
            );
            Err(())
        }
        GenericArgs::AngleBracketed(args) => {
            if args.args.len() != 1 {
                sess.span_err(args.span, "only one type argument is allowed in Rustspec");
                Err(())
            } else {
                match args.args.iter().next() {
                    None => {
                        sess.span_err(
                            args.span,
                            "empty type arguments are not allowed in Rustspec",
                        );
                        Err(())
                    }
                    Some(AngleBracketedArg::Constraint(_)) => {
                        sess.span_err(
                            args.span,
                            "contraint type arguments are not allowed in Rustspec",
                        );
                        Err(())
                    }
                    Some(AngleBracketedArg::Arg(GenericArg::Type(ty))) => {
                        let typ_arg = translate_base_typ(sess, ty).map(|(t, _)| t);
                        Ok((typ_arg?, ty.span))
                    }
                    Some(AngleBracketedArg::Arg(GenericArg::Lifetime(_))) => {
                        sess.span_err(
                            args.span,
                            "lifetime type parameters are not allowed in Rustspect",
                        );
                        Err(())
                    }
                    Some(AngleBracketedArg::Arg(GenericArg::Const(_))) => {
                        sess.span_err(args.span, "const generics are not allowed in Rustspec");
                        Err(())
                    }
                }
            }
        }
    }
}

// TODO: translate paths into base types
fn translate_path(sess: &Session, path: &ast::Path) -> TranslationResult<Path> {
    let location: Vec<TranslationResult<Ident>> = path
        .segments
        .iter()
        .enumerate()
        .map(|(i, segment)| {
            if let Some(_) = segment.args {
                if i + 1 < path.segments.len() {
                    // Only the last segment element should bear arguments
                    sess.span_err(
                        path.span,
                        "type arguments only allowed for the last segment path in Rustspec",
                    );
                    return Err(());
                }
            };
            Ok(segment.ident)
        })
        .collect();
    let location = check_vec(location)?;
    let arg = match path.segments.iter().last() {
        None => {
            sess.span_err(path.span, "empty path are not allowed in Rustspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok(None),
            Some(generic_args) => Ok(Some(Box::new(translate_type_arg(
                sess,
                generic_args,
                &path.span,
            )?.0))),
        },
    };
    Ok(Path {
        location,
        arg: arg?,
    })
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
                        _ => (),
                    },
                    Some(args) => match t.ident.name.to_ident_string().as_str() {
                        "Seq" => {
                            let arg = translate_type_arg(sess, args, &path.span)?;
                            return Ok((BaseTyp::Seq(Box::new(arg)), path.span))
                        }
                        ,
                        _ => (),
                    },
                },
                _ => (),
            };
            Ok((BaseTyp::Named(translate_path(sess, path)?), ty.span))
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
            sess.span_err(ty.span, "trait associated types not allowed in Rustspec");
            Err(())
        }
        TyKind::Rptr(_, _) => {
            sess.span_err(ty.span, "double references not allowed in Rustspec");
            Err(())
        }
        _ => {
            sess.span_err(ty.span, "type not allowed in Rustspec");
            Err(())
        }
    }
}

fn translate_typ(sess: &Session, ty: &Ty) -> TranslationResult<Spanned<Typ>> {
    match &ty.kind {
        TyKind::Rptr(None, mut_ty) => match &mut_ty.mutbl {
            Mutability::Mut => {
                sess.span_err(ty.span, "mutable function arguments are not allowed");
                Err(())
            }
            Mutability::Not => translate_base_typ(sess, &mut_ty.ty)
                .map(|t| (((Borrowing::Borrowed, ty.span), t), ty.span)),
        },
        TyKind::Rptr(Some(_), _) => {
            sess.span_err(ty.span, "lifetime annotations are not allowed in Rustspec");
            Err(())
        }
        _ => translate_base_typ(sess, ty).map(|t| (((Borrowing::Consumed, ty.span), t), ty.span)),
    }
}

enum ExprTranslationResult {
    TransExpr(Expression),
    TransStmt(Statement),
}

fn translate_expr(sess: &Session, e: &Expr) -> TranslationResult<Spanned<ExprTranslationResult>> {
    let translate_expr_expects_exp = |e| match translate_expr(sess, e)? {
        (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
        (ExprTranslationResult::TransStmt(_), span) => {
            sess.span_err(
                span,
                "statements inside expressions are not allowed in Rustspec",
            );
            Err(())
        }
    };
    match &e.kind {
        ExprKind::Binary(op, e1, e2) => Ok((
            ExprTranslationResult::TransExpr(Expression::Binary(
                (op.clone().node, op.clone().span),
                Box::new(translate_expr_expects_exp(e1)?),
                Box::new(translate_expr_expects_exp(e2)?),
            )),
            e.span,
        )),
        ExprKind::Path(Some(_), _) => {
            sess.span_err(e.span, "trait associated values not allowed in Rustspec");
            Err(())
        }
        ExprKind::Path(None, path) => Ok((
            ExprTranslationResult::TransExpr(Expression::Named(translate_path(sess, path)?)),
            e.span,
        )),
        ExprKind::Call(func, args) => {
            let func_path = match &func.kind {
                ExprKind::Path(None, path) => Ok((translate_path(sess, &path)?, path.span)),
                _ => {
                    sess.span_err(
                        func.span,
                        "function expressions are restricted to names only in Rustspec",
                    );
                    Err(())
                }
            };
            let func_args: Vec<TranslationResult<Spanned<Expression>>> = args
                .iter()
                .map(|arg| translate_expr_expects_exp(&arg))
                .collect();
            let func_args = check_vec(func_args);
            Ok((
                ExprTranslationResult::TransExpr(Expression::FuncCall(func_path?, func_args?)),
                e.span,
            ))
        }
        ExprKind::Lit(lit) => match &lit.kind {
            LitKind::Bool(b) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Bool(*b))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Signed(IntTy::I32)) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int32(*x as i32))),
                e.span,
            )),
            LitKind::Int(x, LitIntType::Unsuffixed) => Ok((
                ExprTranslationResult::TransExpr(Expression::Lit(Literal::UnspecifiedInt(*x))),
                e.span,
            )),
            _ => {
                sess.span_err(lit.span, "literal not allowed in Rustspec");
                Err(())
            }
        },
        _ => {
            sess.span_err(e.span, "this expression is not allowed in Rustspec");
            Err(())
        }
    }
}

fn translate_statement(sess: &Session, s: &Stmt) -> TranslationResult<Vec<Spanned<Statement>>> {
    match &s.kind {
        StmtKind::Item(_) => {
            sess.span_err(s.span, "block-local items are not allowed in Rustspec");
            Err(())
        }
        StmtKind::MacCall(_) => {
            sess.span_err(
                s.span,
                "macro calls inside code blocks are not allowed inside Rustspec",
            );
            Err(())
        }
        StmtKind::Empty => {
            sess.span_err(s.span, "empty blocks are not allowed in Rustspec");
            Err(())
        }
        StmtKind::Local(local) => {
            let (id, mutab) = match local.pat.kind {
                PatKind::Ident(BindingMode::ByValue(mutab), id, None) => Ok((id, mutab)),
                _ => {
                    sess.span_err(local.pat.span, "only plain identifier left-hand-side patterns are allowed in Rustspec let bindings");
                    Err(())
                }
            }?;
            let ty: Option<Spanned<Typ>> = match local.ty.clone() {
                None => None,
                Some(ty) => Some(translate_typ(sess, &ty)?),
            };
            let init = match &local.init {
                None => {
                    sess.span_err(
                        local.span,
                        "let-bindings without initialization are not allowed in Rustspec",
                    );
                    Err(())
                }
                Some(e) => match translate_expr(sess, &e)? {
                    (ExprTranslationResult::TransStmt(_), _) => {
                        sess.span_err(
                            e.span,
                            "let binding expression should not contain statements in Rustspec",
                        );
                        Err(())
                    }
                    (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
                },
            }?;
            Ok(vec![(
                Statement::LetBinding(Pattern::IdentPat(id), mutab, ty, init),
                s.span,
            )])
        }
        StmtKind::Expr(e) => {
            let t_s = match translate_expr(sess, &e)? {
                (ExprTranslationResult::TransExpr(e), _) => Ok(Statement::ReturnExp(e)),
                (ExprTranslationResult::TransStmt(_), span) => {
                    sess.span_err(
                        span,
                        "the last expression of a block has to return a value in Rustspec",
                    );
                    Err(())
                }
            };
            Ok(vec![(t_s?, s.span)])
        }
        StmtKind::Semi(e) => {
            let t_s = match translate_expr(sess, &e)? {
                (ExprTranslationResult::TransExpr(e), span) => {
                    Statement::LetBinding(Pattern::WildCard, Mutability::Not, None, (e, span))
                }
                (ExprTranslationResult::TransStmt(s), _) => s,
            };
            Ok(vec![(t_s, s.span)])
        }
    }
}

fn translate_block(sess: &Session, b: &ast::Block) -> TranslationResult<Spanned<Block>> {
    match b.rules {
        BlockCheckMode::Unsafe(_) => {
            sess.span_err(b.span, "unsafe blocks are not allowed in Rustspec");
            return Err(());
        }
        BlockCheckMode::Default => (),
    };
    let stmts = b
        .stmts
        .iter()
        .map(|s| translate_statement(sess, &s))
        .collect();
    let stmts = check_vec(stmts)?.into_iter().flatten().collect();
    Ok((stmts, b.span))
}

fn translate_items(sess: &Session, i: &ast::Item) -> TranslationResult<Item> {
    match i.kind {
        ItemKind::Fn(defaultness, ref sig, ref generics, ref body) => {
            // First, checking that no fancy function qualifier is here
            match defaultness {
                Defaultness::Default(span) => {
                    sess.span_err(span, "\"default\" keyword not allowed in Rustspec")
                }
                _ => (),
            }
            match sig.header.unsafety {
                Unsafe::No => (),
                Unsafe::Yes(span) => {
                    sess.span_err(span, "unsafe functions not allowed in Rustspec");
                }
            }
            match sig.header.asyncness {
                Async::No => (),
                Async::Yes { span, .. } => {
                    sess.span_err(span, "async functions not allowed in Rustspec");
                }
            }
            match sig.header.constness {
                Const::No => (),
                Const::Yes(span) => {
                    sess.span_err(span, "const functions not allowed in Rustspec");
                }
            }
            match sig.header.ext {
                Extern::None => (),
                _ => {
                    sess.span_err(i.span, "extern functions not allowed in Rustspec");
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
                            Ok((id, param.pat.span))
                        }
                        _ => {
                            sess.span_err(
                            param.pat.span,
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
                sess.span_err(generics.span, "generics are not allowed in Rustspec");
            };
            let fn_inputs = check_vec(fn_inputs)?;
            let fn_output = match &sig.decl.output {
                FnRetTy::Default(span) => (BaseTyp::Unit, span.clone()),
                FnRetTy::Ty(ty) => translate_base_typ(sess, ty)?,
            };
            let fn_body: Spanned<Block> = match body {
                None => (Vec::new(), i.span),
                Some(b) => translate_block(sess, &b)?,
            };
            let fn_sig = FuncSig {
                args: fn_inputs,
                ret: fn_output,
            };
            Ok(Item::FnDecl((i.ident, fn_sig, fn_body)))
        }
        _ => panic!(),
    }
}

pub fn translate(sess: &Session, krate: &Crate) -> TranslationResult<Program> {
    let items = &krate.module.items;
    check_vec(
        items
            .into_iter()
            .map(|i| Ok((translate_items(sess, &i)?, i.span)))
            .collect(),
    )
}
