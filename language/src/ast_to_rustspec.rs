use im::{HashMap, HashSet};
use rustc_ast::{
    ast::{
        self, AngleBracketedArg, Async, Attribute, BindingMode, BlockCheckMode, BorrowKind, Const,
        Crate, Defaultness, Expr, ExprKind, Extern, Fn as FnKind, FnRetTy, GenericArg, GenericArgs,
        IntTy, ItemKind, LitIntType, LitKind, LocalKind, MacArgs, MacCall, Mutability, Pat,
        PatKind, RangeLimits, Stmt, StmtKind, StrStyle, Ty, TyAlias as TyAliasKind, TyKind, UintTy,
        UnOp, Unsafe, UseTreeKind, VariantData,
    },
    node_id::NodeId,
    token::{DelimToken, LitKind as TokenLitKind, TokenKind},
    tokenstream::{TokenStream, TokenTree},
};
use rustc_session::Session;
use rustc_span::{symbol, Span};

use crate::hir_to_rustspec::ExternalData;
use crate::rustspec::*;
use crate::HacspecErrorEmitter;

#[derive(Clone)]
pub struct SpecialNames {
    pub arrays: HashSet<String>,
    pub enums: HashSet<String>,
    pub aliases: HashMap<String, BaseTyp>,
}

fn dealias_probable_enum_name(
    s: String,
    specials: &SpecialNames,
    incoming_args: Option<Vec<Spanned<BaseTyp>>>,
) -> Option<(String, Option<Vec<Spanned<BaseTyp>>>)> {
    match specials.aliases.get(&s) {
        None => (),
        Some(t) => match t {
            BaseTyp::Named(
                (
                    TopLevelIdent {
                        string: name,
                        kind: TopLevelIdentKind::Type,
                    },
                    _,
                ),
                args,
            ) => {
                if *name != s {
                    return dealias_probable_enum_name(name.clone(), specials, args.clone());
                }
            }
            _ => (),
        },
    };
    if specials.enums.contains(&s) {
        Some((s, incoming_args))
    } else {
        None
    }
}

type TranslationResult<T> = Result<T, ()>;

fn check_vec<T>(v: Vec<TranslationResult<T>>) -> TranslationResult<Vec<T>> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn translate_toplevel_ident(i: &symbol::Ident, kind: TopLevelIdentKind) -> Spanned<TopLevelIdent> {
    (
        TopLevelIdent {
            string: i.name.to_ident_string(),
            kind,
        },
        i.span.into(),
    )
}

fn translate_ident(i: &symbol::Ident) -> Spanned<Ident> {
    (Ident::Unresolved(i.name.to_ident_string()), i.span.into())
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
                "parenthesized path arguments are not allowed in Hacspec",
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
                            "contraint type arguments are not allowed in Hacspec",
                        );
                        Err(())
                    }
                    AngleBracketedArg::Arg(GenericArg::Type(ty)) => {
                        let typ_arg = translate_base_typ(sess, ty).map(|(t, _)| t);
                        Ok((typ_arg?, ty.span.into()))
                    }
                    AngleBracketedArg::Arg(GenericArg::Lifetime(_)) => {
                        sess.span_rustspec_err(
                            args.span,
                            "lifetime type parameters are not allowed in Hacspect",
                        );
                        Err(())
                    }
                    AngleBracketedArg::Arg(GenericArg::Const(_)) => {
                        sess.span_rustspec_err(
                            args.span,
                            "const generics are not allowed in Hacspec",
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
            sess.span_rustspec_err(path.span, "empty path are not allowed in Hacspec");
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
) -> TranslationResult<(Spanned<TopLevelIdent>, Option<Vec<Spanned<BaseTyp>>>)> {
    if path.segments.len() > 1 {
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty path are not allowed in Hacspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok((
                translate_toplevel_ident(&segment.ident, TopLevelIdentKind::Type),
                None,
            )),
            Some(generic_args) => Ok((
                translate_toplevel_ident(&segment.ident, TopLevelIdentKind::Type),
                Some(translate_type_args(sess, generic_args, &path.span)?),
            )),
        },
    }
}

fn translate_expr_name(
    sess: &Session,
    path: &ast::Path,
    span: &Span,
    _specials: &SpecialNames,
) -> TranslationResult<Spanned<ExprTranslationResult>> {
    if path.segments.len() > 2 {
        sess.span_rustspec_err(
            path.span,
            "a path that has more than 2 segments is forbidden in Hacspec",
        );
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty identifiers are not allowed in Hacspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok((
                ExprTranslationResult::TransExpr(Expression::Named(
                    translate_ident(&segment.ident).0,
                )),
                span.clone().into(),
            )),
            Some(_) => {
                sess.span_rustspec_err(path.span, "expression identifiers cannot have arguments");
                Err(())
            }
        },
    }
}

pub fn translate_struct_name(sess: &Session, path: &ast::Path) -> TranslationResult<TopLevelIdent> {
    if path.segments.len() > 1 {
        sess.span_rustspec_err(path.span, "expected a single-segment struct name");
        return Err(());
    }
    match path.segments.iter().last() {
        None => {
            sess.span_rustspec_err(path.span, "empty identifiers are not allowed in Hacspec");
            Err(())
        }
        Some(segment) => match &segment.args {
            None => Ok(TopLevelIdent {
                string: segment.ident.name.to_ident_string(),
                kind: TopLevelIdentKind::Type,
            }),
            Some(_) => {
                sess.span_rustspec_err(path.span, "expression identifiers cannot have arguments");
                Err(())
            }
        },
    }
}

enum FuncNameResult {
    TypePrefixed(Option<Spanned<BaseTyp>>, Spanned<TopLevelIdent>),
    EnumConstructor(BaseTyp, Spanned<TopLevelIdent>),
}

fn translate_func_name(
    sess: &Session,
    specials: &SpecialNames,
    path: &ast::Path,
) -> TranslationResult<FuncNameResult> {
    if path.segments.len() > 2 {
        return Err(());
    }
    if path.segments.len() == 2 {
        match path.segments.first() {
            None => panic!(), // should not happen
            Some(segment) => {
                let segment_string = segment.ident.name.to_ident_string();
                if let Some((enum_name, enum_args)) =
                    dealias_probable_enum_name(segment_string, specials, None)
                {
                    Ok(FuncNameResult::EnumConstructor(
                        BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: enum_name,
                                    kind: TopLevelIdentKind::Type,
                                },
                                segment.ident.span.clone().into(),
                            ),
                            match segment.args {
                                None => enum_args,
                                Some(ref args) => {
                                    Some(translate_type_args(sess, args, &segment.ident.span)?)
                                }
                            },
                        ),
                        translate_toplevel_ident(
                            &path.segments.last().unwrap().ident,
                            TopLevelIdentKind::EnumConstructor,
                        ),
                    ))
                } else {
                    Ok(FuncNameResult::TypePrefixed(
                        Some(translate_base_typ(
                            sess,
                            &ast::Ty {
                                tokens: path.tokens.clone(),
                                span: path.span,
                                id: NodeId::MAX,
                                kind: TyKind::Path(
                                    None,
                                    ast::Path {
                                        tokens: path.tokens.clone(),
                                        span: path.span,
                                        segments: vec![segment.clone()],
                                    },
                                ),
                            },
                        )?),
                        translate_toplevel_ident(
                            &path.segments.last().unwrap().ident,
                            TopLevelIdentKind::Function,
                        ),
                    ))
                }
            }
        }
    } else {
        Ok(FuncNameResult::TypePrefixed(
            None,
            translate_toplevel_ident(
                &path.segments.last().unwrap().ident,
                TopLevelIdentKind::Function,
            ),
        ))
    }
}

fn translate_base_typ(sess: &Session, ty: &Ty) -> TranslationResult<Spanned<BaseTyp>> {
    match &ty.kind {
        TyKind::Path(None, path) => {
            match &path.segments.as_slice() {
                [t] => match &t.args {
                    None => match t.ident.name.to_ident_string().as_str() {
                        "u32" => return Ok((BaseTyp::UInt32, ty.span.into())),
                        "i32" => return Ok((BaseTyp::Int32, ty.span.into())),
                        "u8" => return Ok((BaseTyp::UInt8, ty.span.into())),
                        "i8" => return Ok((BaseTyp::Int8, ty.span.into())),
                        "u16" => return Ok((BaseTyp::UInt16, ty.span.into())),
                        "i16" => return Ok((BaseTyp::Int16, ty.span.into())),
                        "u64" => return Ok((BaseTyp::UInt64, ty.span.into())),
                        "i64" => return Ok((BaseTyp::Int64, ty.span.into())),
                        "u128" => return Ok((BaseTyp::UInt128, ty.span.into())),
                        "i128" => return Ok((BaseTyp::Int128, ty.span.into())),
                        "bool" => return Ok((BaseTyp::Bool, ty.span.into())),
                        "usize" => return Ok((BaseTyp::Usize, ty.span.into())),
                        "isize" => return Ok((BaseTyp::Isize, ty.span.into())),
                        "Seq" => {
                            sess.span_rustspec_err(ty.span, "Seq expects a type argument");
                            return Err(());
                        }
                        _ => (),
                    },
                    Some(args) => match t.ident.name.to_ident_string().as_str() {
                        "Seq" | "PublicSeq" | "SecretSeq" => {
                            let args = translate_type_args(sess, args, &path.span.into())?;
                            if args.len() > 1 {
                                sess.span_rustspec_err(
                                    ty.span.clone(),
                                    "Seq cannot have multiple type arguments",
                                );
                                return Err(());
                            }
                            return Ok((
                                BaseTyp::Seq(Box::new(args.first().unwrap().clone())),
                                path.span.into(),
                            ));
                        }
                        _ => (),
                    },
                },
                _ => (),
            };
            let (name, arg) = translate_typ_name(sess, path)?;
            Ok((BaseTyp::Named(name, arg), ty.span.into()))
        }
        TyKind::Tup(tys) => {
            let rtys: Vec<TranslationResult<Spanned<BaseTyp>>> = tys
                .into_iter()
                .map(|ty| translate_base_typ(sess, ty))
                .collect();
            let rtys = check_vec(rtys)?;
            Ok((BaseTyp::Tuple(rtys), ty.span.into()))
        }
        TyKind::Path(Some(_), _) => {
            sess.span_rustspec_err(ty.span, "trait associated types not allowed in Hacspec");
            Err(())
        }
        TyKind::Rptr(_, _) => {
            sess.span_rustspec_err(ty.span, "double references not allowed in Hacspec");
            Err(())
        }
        _ => {
            sess.span_rustspec_err(ty.span, "type not allowed in Hacspec");
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
                .map(|t| (((Borrowing::Borrowed, ty.span.into()), t), ty.span.into())),
        },
        TyKind::Rptr(Some(_), _) => {
            sess.span_rustspec_err(ty.span, "lifetime annotations are not allowed in Hacspec");
            Err(())
        }
        _ => translate_base_typ(sess, ty)
            .map(|t| (((Borrowing::Consumed, ty.span.into()), t), ty.span.into())),
    }
}

enum ExprTranslationResult {
    TransExpr(Expression),
    TransStmt(Statement),
}

fn translate_expr_expects_exp(
    sess: &Session,
    specials: &SpecialNames,
    e: &Expr,
) -> TranslationResult<Spanned<Expression>> {
    match translate_expr(sess, specials, e)? {
        (ExprTranslationResult::TransExpr(e), span) => Ok((e, span)),
        (ExprTranslationResult::TransStmt(_), span) => {
            sess.span_rustspec_err(
                span,
                "statements inside expressions are not allowed in Hacspec",
            );
            Err(())
        }
    }
}

fn translate_function_argument(
    sess: &Session,
    specials: &SpecialNames,
    e: &Expr,
) -> TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)> {
    match &e.kind {
        ExprKind::AddrOf(BorrowKind::Ref, is_mut, e1) => match is_mut {
            Mutability::Mut => {
                sess.span_rustspec_err(e.span, "mutable borrows are forbidden in Hacspec");
                Err(())
            }
            Mutability::Not => Ok((
                translate_expr_expects_exp(sess, specials, e1)?,
                (Borrowing::Borrowed, e.span.clone().into()),
            )),
        },
        _ => Ok((
            translate_expr_expects_exp(sess, specials, e)?,
            (Borrowing::Consumed, e.span.clone().into()),
        )),
    }
}

fn translate_literal(
    sess: &Session,
    lit: &rustc_ast::Lit,
    span: Span,
) -> TranslationResult<Spanned<ExprTranslationResult>> {
    match &lit.kind {
        LitKind::Bool(b) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Bool(*b))),
            span.into(),
        )),
        //TODO: check that the casting is safe each time!
        LitKind::Int(x, LitIntType::Signed(IntTy::I128)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int128(*x as i128))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::U128)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt128(*x as u128))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Signed(IntTy::I64)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int64(*x as i64))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::U64)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt64(*x as u64))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Signed(IntTy::I32)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int32(*x as i32))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::U32)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt32(*x as u32))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Signed(IntTy::I16)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int16(*x as i16))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::U16)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt16(*x as u16))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Signed(IntTy::I8)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Int8(*x as i8))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::U8)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::UInt8(*x as u8))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Signed(IntTy::Isize)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Isize(*x as isize))),
            span.into(),
        )),
        LitKind::Int(x, LitIntType::Unsigned(UintTy::Usize)) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Usize(*x as usize))),
            span.into(),
        )),
        // Unspecified integers are always interpreted as usize
        LitKind::Int(x, LitIntType::Unsuffixed) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Usize(*x as usize))),
            span.into(),
        )),
        LitKind::Str(msg, StrStyle::Cooked) => Ok((
            ExprTranslationResult::TransExpr(Expression::Lit(Literal::Str(msg.to_ident_string()))),
            span.into(),
        )),
        _ => {
            sess.span_rustspec_err(lit.span, "literal not allowed in Hacspec");
            Err(())
        }
    }
}

fn translate_binop(x: ast::BinOpKind) -> BinOpKind {
    match x {
        ast::BinOpKind::Add => BinOpKind::Add,
        ast::BinOpKind::Sub => BinOpKind::Sub,
        ast::BinOpKind::Mul => BinOpKind::Mul,
        ast::BinOpKind::Div => BinOpKind::Div,
        ast::BinOpKind::Rem => BinOpKind::Rem,
        ast::BinOpKind::And => BinOpKind::And,
        ast::BinOpKind::Or => BinOpKind::Or,
        ast::BinOpKind::BitXor => BinOpKind::BitXor,
        ast::BinOpKind::BitAnd => BinOpKind::BitAnd,
        ast::BinOpKind::BitOr => BinOpKind::BitOr,
        ast::BinOpKind::Shl => BinOpKind::Shl,
        ast::BinOpKind::Shr => BinOpKind::Shr,
        ast::BinOpKind::Eq => BinOpKind::Eq,
        ast::BinOpKind::Lt => BinOpKind::Lt,
        ast::BinOpKind::Le => BinOpKind::Le,
        ast::BinOpKind::Ne => BinOpKind::Ne,
        ast::BinOpKind::Ge => BinOpKind::Ge,
        ast::BinOpKind::Gt => BinOpKind::Gt,
    }
}

fn translate_expr(
    sess: &Session,
    specials: &SpecialNames,
    e: &Expr,
) -> TranslationResult<Spanned<ExprTranslationResult>> {
    match &e.kind {
        ExprKind::Binary(op, e1, e2) => Ok((
            ExprTranslationResult::TransExpr(Expression::Binary(
                (translate_binop(op.clone().node), op.clone().span.into()),
                Box::new(translate_expr_expects_exp(sess, specials, e1)?),
                Box::new(translate_expr_expects_exp(sess, specials, e2)?),
                None,
            )),
            e.span.into(),
        )),
        ExprKind::Unary(op, e1) => Ok((
            ExprTranslationResult::TransExpr(Expression::Unary(
                match *op {
                    UnOp::Not => UnOpKind::Not,
                    UnOp::Neg => UnOpKind::Neg,
                    UnOp::Deref => {
                        sess.span_rustspec_err(e.span, "dereferences not allowed in Hacspec");
                        return Err(());
                    }
                },
                Box::new(translate_expr_expects_exp(sess, specials, e1)?),
                None,
            )),
            e.span.into(),
        )),
        ExprKind::Path(Some(_), _) => {
            sess.span_rustspec_err(e.span, "trait associated values not allowed in Hacspec");
            Err(())
        }
        ExprKind::Path(None, ast::Path { segments, .. })
            if segments.len() == 2
                && specials
                    .enums
                    .contains(&segments.iter().next().unwrap().ident.name.to_ident_string()) =>
        {
            // This is the case of enum injection
            let mut it = segments.iter();
            let first_seg = it.next().unwrap();
            let second_seg = it.next().unwrap();
            if second_seg.args.is_some() {
                sess.span_rustspec_err(
                    second_seg.ident.span,
                    "the name of the enum case should not have any arguments",
                );
                return Err(());
            }
            Ok((
                ExprTranslationResult::TransExpr(Expression::EnumInject(
                    BaseTyp::Named(
                        translate_toplevel_ident(&first_seg.ident, TopLevelIdentKind::Type),
                        match &first_seg.args {
                            None => None,
                            Some(args) => {
                                Some(translate_type_args(sess, &*args, &first_seg.ident.span)?)
                            }
                        },
                    ),
                    translate_toplevel_ident(&second_seg.ident, TopLevelIdentKind::EnumConstructor),
                    None,
                )),
                e.span.into(),
            ))
        }
        ExprKind::Path(None, path) => translate_expr_name(sess, path, &e.span, specials),
        ExprKind::Call(func, args) => {
            let func_name_kind = match &func.kind {
                ExprKind::Path(None, path) => Ok(translate_func_name(sess, specials, &path)?),
                _ => {
                    sess.span_rustspec_err(
                        func.span,
                        "function expressions are restricted to names only in Hacspec",
                    );
                    Err(())
                }
            }?;
            match func_name_kind {
                FuncNameResult::TypePrefixed(func_prefix, func_name) => {
                    let func_name_string = (func_name.clone().0).string;
                    let func_name_but_as_type = (
                        TopLevelIdent {
                            string: func_name.0.string.clone(),
                            kind: TopLevelIdentKind::Type,
                        },
                        func_name.1,
                    );
                    let func_name_but_as_enum_constructor = (
                        TopLevelIdent {
                            string: func_name.0.string.clone(),
                            kind: TopLevelIdentKind::EnumConstructor,
                        },
                        func_name.1,
                    );
                    if specials.enums.contains(&func_name_string) {
                        // Special case for struct constructors
                        let func_args: Vec<
                            TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)>,
                        > = args
                            .iter()
                            .map(|arg| translate_function_argument(sess, specials, &arg))
                            .collect();
                        let func_args = check_vec(func_args)?;
                        let func_args = check_vec(
                            func_args
                                .into_iter()
                                .map(|(arg, borrow)| match &borrow.0 {
                                    Borrowing::Consumed => Ok(arg),
                                    Borrowing::Borrowed => {
                                        sess.span_rustspec_err(
                                            borrow.1.clone(),
                                            "struct arguments cannot be borrowed in Hacspec",
                                        );
                                        Err(())
                                    }
                                })
                                .collect(),
                        )?;
                        return Ok((
                            ExprTranslationResult::TransExpr(Expression::EnumInject(
                                BaseTyp::Named(func_name_but_as_type, None),
                                func_name_but_as_enum_constructor,
                                Some(if func_args.len() > 1 {
                                    (Box::new(Expression::Tuple(func_args)), e.span.into())
                                } else {
                                    let arg = func_args.into_iter().next().unwrap();
                                    (Box::new(arg.0), arg.1)
                                }),
                            )),
                            e.span.into(),
                        ));
                    }
                    if specials.arrays.contains(&func_name_string) {
                        // Special case for array constructors
                        if args.len() != 1 {
                            sess.span_rustspec_err(
                                e.span,
                                "array constructor called with more than one arguments",
                            );
                            return Err(());
                        }
                        match &args.first().unwrap().kind {
                            // First case: the array itself
                            ExprKind::Array(cells) => {
                                let new_cells: Vec<TranslationResult<Spanned<Expression>>> = cells
                                    .iter()
                                    .map(|cell| translate_expr_expects_exp(sess, specials, &cell))
                                    .collect();
                                let new_cells = check_vec(new_cells)?;
                                return Ok((
                                    (ExprTranslationResult::TransExpr(Expression::NewArray(
                                        Some(func_name_but_as_type),
                                        None,
                                        new_cells,
                                    ))),
                                    e.span.into(),
                                ));
                            }
                            // Second case: a call to the secret_array! macro
                            ExprKind::MacCall(call) => {
                                if call.path.segments.len() > 1 {
                                    sess.span_rustspec_err(
                                        call.path.span,
                                        "cannot use macros other than the ones defined by Hacspec",
                                    );
                                    return Err(());
                                }
                                let name = call.path.segments.first().unwrap();
                                match (
                                    name.ident.name.to_ident_string().as_str(),
                                    name.args.as_ref(),
                                ) {
                                    ("secret_array", None) => match &*call.args {
                                        MacArgs::Delimited(_, _, tokens) => {
                                            let mut it = tokens.trees();
                                            let (first_arg, second_arg, third_arg) = {
                                                let first_arg =
                                                    it.next().map_or(Err(()), |x| Ok(x));
                                                let second_arg =
                                                    it.next().map_or(Err(()), |x| Ok(x));
                                                let third_arg =
                                                    it.next().map_or(Err(()), |x| Ok(x));
                                                Ok((first_arg?, second_arg?, third_arg?))
                                            }?;
                                            let typ_ident = check_for_toplevel_ident(
                                                sess,
                                                &first_arg,
                                                TopLevelIdentKind::Type,
                                            )?;
                                            check_for_comma(sess, &second_arg)?;
                                            let array = check_for_literal_array(sess, &third_arg)?;
                                            let array = array
                                                .into_iter()
                                                .map(|i| {
                                                    (
                                                        Expression::FuncCall(
                                                            None,
                                                            typ_ident.0.clone(),
                                                            vec![(
                                                                i.clone(),
                                                                (Borrowing::Consumed, i.1.clone()),
                                                            )],
                                                        ),
                                                        i.1.clone(),
                                                    )
                                                })
                                                .collect();
                                            return Ok((
                                                (ExprTranslationResult::TransExpr(
                                                    Expression::NewArray(
                                                        Some(func_name_but_as_type),
                                                        None,
                                                        array,
                                                    ),
                                                )),
                                                e.span.into(),
                                            ));
                                        }
                                        _ => {
                                            sess.span_rustspec_err(
                                                call.args.span().unwrap().clone(),
                                                "expected parenthesis-delimited args",
                                            );
                                            return Err(());
                                        }
                                    },
                                    ("secret_bytes", None) => match &*call.args {
                                        MacArgs::Delimited(_, _, tokens) => {
                                            let mut it = tokens.trees();
                                            let first_arg = it.next().map_or(Err(()), |x| Ok(x))?;
                                            let array = check_for_literal_array(sess, &first_arg)?;
                                            let array = array
                                                .into_iter()
                                                .map(|i| {
                                                    (
                                                        Expression::FuncCall(
                                                            None,
                                                            (U8_TYP(), call.span().into()),
                                                            vec![(
                                                                i.clone(),
                                                                (Borrowing::Consumed, i.1.clone()),
                                                            )],
                                                        ),
                                                        i.1.clone(),
                                                    )
                                                })
                                                .collect();
                                            return Ok((
                                                (ExprTranslationResult::TransExpr(
                                                    Expression::NewArray(
                                                        Some(func_name_but_as_type),
                                                        None,
                                                        array,
                                                    ),
                                                )),
                                                e.span.into(),
                                            ));
                                        }
                                        _ => {
                                            sess.span_rustspec_err(
                                                call.args.span().unwrap().clone(),
                                                "expected parenthesis-delimited args",
                                            );
                                            return Err(());
                                        }
                                    },
                                    _ => {
                                        sess.span_rustspec_err(
                                            call.path.span.clone(),
                                            "only the secret_array! macro can be called here",
                                        );
                                        return Err(());
                                    }
                                }
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
                    let func_args: Vec<
                        TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)>,
                    > = args
                        .iter()
                        .map(|arg| translate_function_argument(sess, specials, &arg))
                        .collect();
                    let func_args = check_vec(func_args)?;
                    Ok((
                        ExprTranslationResult::TransExpr(Expression::FuncCall(
                            func_prefix,
                            func_name,
                            func_args,
                        )),
                        e.span.into(),
                    ))
                }
                FuncNameResult::EnumConstructor(enum_name, enum_case) => {
                    let func_args: Vec<TranslationResult<Spanned<Expression>>> = args
                        .iter()
                        .map(|arg| translate_expr_expects_exp(sess, specials, &arg))
                        .collect();
                    let func_args = check_vec(func_args)?;
                    Ok((
                        ExprTranslationResult::TransExpr(Expression::EnumInject(
                            enum_name,
                            enum_case,
                            Some((
                                Box::new(if func_args.len() == 1 {
                                    func_args.iter().next().unwrap().0.clone()
                                } else {
                                    Expression::Tuple(func_args)
                                }),
                                e.span.clone().into(),
                            )),
                        )),
                        e.span.into(),
                    ))
                }
            }
        }
        ExprKind::MethodCall(method_name, args, span) => {
            let func_args: Vec<TranslationResult<(Spanned<Expression>, Spanned<Borrowing>)>> = args
                .iter()
                .map(|arg| translate_function_argument(sess, specials, &arg))
                .collect();
            let func_args = check_vec(func_args)?;
            let (method_arg, rest_args) = func_args.split_at(1);
            let method_arg = method_arg
                .first()
                .map_or(Err(()), |x| Ok(Box::new(x.clone())))?;
            let method_name = match method_name.args {
                None => Ok(translate_toplevel_ident(
                    &method_name.ident,
                    TopLevelIdentKind::Function,
                )),
                Some(_) => {
                    sess.span_rustspec_err(*span, "method type arguments not allowed in Hacspec");
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
                e.span.into(),
            ))
        }
        ExprKind::Lit(lit) => translate_literal(sess, lit, e.span.clone()),
        ExprKind::Assign(lhs, rhs_e, _) => {
            let (r_e, r_e_question_mark) =
                match translate_expr_accepts_question_mark(sess, specials, &rhs_e)? {
                    (ExprTranslationResultMaybeQuestionMark::TransStmt(_), _) => {
                        sess.span_rustspec_err(
                            e.span,
                            "assignment expressions should not contain statements in Hacspec",
                        );
                        return Err(());
                    }
                    (ExprTranslationResultMaybeQuestionMark::TransExpr(e, question_mark), span) => {
                        ((e, span), question_mark)
                    }
                };
            match &lhs.kind {
                ExprKind::Path(None, path) => match &path.segments.as_slice() {
                    [var] => match &var.args {
                        None => {
                            let id = translate_ident(&var.ident);
                            Ok((
                                ExprTranslationResult::TransStmt(Statement::Reassignment(
                                    id,
                                    r_e,
                                    r_e_question_mark,
                                )),
                                e.span.into(),
                            ))
                        }
                        Some(_) => {
                            sess.span_rustspec_err(path.span, "no arguments expected in Hacspec");
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
                    let r_index = translate_expr(sess, specials, index)?;
                    let r_index = match r_index {
                        (ExprTranslationResult::TransStmt(_), span) => {
                            sess.span_rustspec_err(
                                span,
                                "statements not allowed in Hacspec for assignments left-hand-sides",
                            );
                            Err(())
                        }
                        (ExprTranslationResult::TransExpr(r_index), span) => Ok((r_index, span)),
                    };
                    match &a.kind {
                        ExprKind::Path(None, path) => match path.segments.as_slice() {
                            [var] => match &var.args {
                                None => {
                                    let id = translate_ident(&var.ident);
                                    Ok((
                                        ExprTranslationResult::TransStmt(Statement::ArrayUpdate(
                                            id,
                                            r_index?,
                                            r_e,
                                            r_e_question_mark,
                                            None,
                                        )),
                                        e.span.into(),
                                    ))
                                }
                                Some(_) => {
                                    sess.span_rustspec_err(
                                        path.span,
                                        "no arguments expected in Hacspec",
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
                            sess.span_rustspec_err(a.span, "Hacspect only allows array updates on arrays that are explicitely let-binded in a variable");
                            Err(())
                        }
                    }
                }
                _ => {
                    sess.span_rustspec_err(
                        lhs.span,
                        "left-hand side of the assignment must be variables in Hacspec",
                    );
                    Err(())
                }
            }
        }
        ExprKind::If(cond, t_e, f_e) => {
            let r_cond = match translate_expr(sess, specials, cond)? {
                (ExprTranslationResult::TransStmt(_), span) => {
                    sess.span_rustspec_err(
                        span,
                        "statements not allowed inside conditions in Hacspec",
                    );
                    Err(())
                }
                (ExprTranslationResult::TransExpr(r_cond), span) => Ok((r_cond, span)),
            }?;
            let mut r_t_e = translate_block(sess, specials, t_e)?;
            let r_f_e = match f_e {
                None => Ok(None),
                Some(f_e) => match &f_e.kind {
                    ExprKind::Block(f_e, _) => {
                        let r_f_e = translate_block(sess, specials, f_e)?;
                        Ok(Some(r_f_e))
                    }
                    _ => {
                        sess.span_rustspec_err(
                            f_e.span,
                            "block of statements expected in the else branch in Hacspec",
                        );
                        Err(())
                    }
                },
            }?;
            let stmt_result = (
                ExprTranslationResult::TransStmt(Statement::Conditional(
                    r_cond.clone(),
                    r_t_e.clone(),
                    r_f_e.clone(),
                    None,
                )),
                e.span.into(),
            );
            // Now, we determine whether what we have translate is an inline conditional
            // or a statement-like conditional
            match r_f_e {
                Some(mut r_f_e) => {
                    if r_t_e.0.stmts.len() == 1 && r_f_e.0.stmts.len() == 1 {
                        let r_t_span = r_t_e.1.clone();
                        let r_f_span = r_f_e.1.clone();
                        let r_t_e = r_t_e.0.stmts.pop().unwrap();
                        let r_f_e = r_f_e.0.stmts.pop().unwrap();
                        match (r_t_e, r_f_e) {
                            (
                                (Statement::ReturnExp(r_t_e), _),
                                (Statement::ReturnExp(r_f_e), _),
                            ) => Ok((
                                ExprTranslationResult::TransExpr(Expression::InlineConditional(
                                    Box::new(r_cond),
                                    Box::new((r_t_e, r_t_span)),
                                    Box::new((r_f_e, r_f_span)),
                                )),
                                e.span.into(),
                            )),
                            _ => Ok(stmt_result),
                        }
                    } else {
                        Ok(stmt_result)
                    }
                }
                _ => Ok(stmt_result),
            }
        }
        ExprKind::ForLoop(pat, range, b, _) => {
            let id = match &pat.kind {
                PatKind::Ident(BindingMode::ByValue(Mutability::Not), id, None) => {
                    Ok(Some(translate_ident(id)))
                }
                PatKind::Wild => Ok(None),
                _ => {
                    sess.span_rustspec_err(
                        pat.span,
                        "only single-variable-binding patterns are allowed for loops in Hacspec",
                    );
                    Err(())
                }
            };
            let e_begin_end = match &range.kind {
                ExprKind::Range(Some(r_begin), Some(r_end), RangeLimits::HalfOpen) => {
                    let e_begin = translate_expr(sess, specials, r_begin)?;
                    let e_end = translate_expr(sess, specials, r_end)?;
                    match (e_begin, e_end) {
                        (
                            (ExprTranslationResult::TransExpr(e_begin), span_begin),
                            (ExprTranslationResult::TransExpr(e_end), span_end),
                        ) => Ok(((e_begin, span_begin), (e_end, span_end))),
                        _ => {
                            sess.span_rustspec_err(
                                range.span,
                                "range expressions cannot contain statements in Hacspec",
                            );
                            Err(())
                        }
                    }
                }
                _ => {
                    sess.span_rustspec_err(
                        range.span,
                        "expected a non-inclusive range expression here in Hacspec",
                    );
                    Err(())
                }
            };
            let (e_begin, e_end) = e_begin_end?;
            let r_b = translate_block(sess, specials, b)?;
            Ok((
                ExprTranslationResult::TransStmt(Statement::ForLoop(id?, e_begin, e_end, r_b)),
                e.span.into(),
            ))
        }
        ExprKind::Index(a, e2) => match &a.kind {
            ExprKind::Path(None, path) => match path.segments.as_slice() {
                [var] => match &var.args {
                    None => {
                        let id = translate_ident(&var.ident);
                        let r_e2 = translate_expr(sess, specials, e2)?;
                        match r_e2 {
                            (ExprTranslationResult::TransExpr(r_e2), r_e2_span) => Ok((
                                ExprTranslationResult::TransExpr(Expression::ArrayIndex(
                                    id,
                                    Box::new((r_e2, r_e2_span)),
                                    None,
                                )),
                                e.span.into(),
                            )),
                            _ => {
                                sess.span_rustspec_err(
                                        e.span,
                                        "statements not allowed in Hacspec inside array indexing expression",
                                    );
                                Err(())
                            }
                        }
                    }
                    Some(_) => {
                        sess.span_rustspec_err(path.span, "no arguments expected in Hacspec");
                        Err(())
                    }
                },
                _ => {
                    sess.span_rustspec_err(path.span, "can only index local arrays");
                    Err(())
                }
            },
            _ => {
                sess.span_rustspec_err(a.span, "Hacspect only allows array indexing on arrays that are explicitely let-binded in a variable");
                Err(())
            }
        },
        ExprKind::Tup(args) => {
            let r_args = args
                .into_iter()
                .map(|arg| match translate_expr(sess, specials, arg)? {
                    (ExprTranslationResult::TransExpr(r_arg), r_span) => Ok((r_arg, r_span)),
                    (ExprTranslationResult::TransStmt(_), r_span) => {
                        sess.span_rustspec_err(
                            r_span,
                            "statements forbidden in tuple expressions in Hacspec",
                        );
                        Err(())
                    }
                })
                .collect();
            let r_args = check_vec(r_args)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::Tuple(r_args)),
                e.span.into(),
            ))
        }
        ExprKind::Struct(_) => {
            sess.span_rustspec_err(e.span.clone(), "structs are not supported yet in Hacspec");
            Err(())
        }
        ExprKind::Box(_) => {
            sess.span_rustspec_err(e.span.clone(), "boxing is not allowed in Hacspec");
            Err(())
        }
        ExprKind::Array(_) => {
            sess.span_rustspec_err(e.span.clone(), "array values are not allowed in Hacspec");
            Err(())
        }
        ExprKind::Cast(e1, t1) => {
            let new_e1 = translate_expr_expects_exp(sess, specials, e1)?;
            let new_t1 = translate_base_typ(sess, t1)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::IntegerCasting(
                    Box::new(new_e1),
                    new_t1,
                    None,
                )),
                e.span.clone().into(),
            ))
        }
        ExprKind::Type(_, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "type expressions are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Let(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "inline lets are not allowed in Hacspec");
            Err(())
        }
        ExprKind::While(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "while loops are not allowed in Hacspec");
            Err(())
        }
        ExprKind::Loop(_, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "undecorated loops are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Match(e1, arms) => {
            let e1 = translate_expr_expects_exp(sess, specials, e1)?;
            let arms = check_vec(
                arms.iter()
                    .map(|arm| {
                        if arm.guard.is_some() {
                            sess.span_rustspec_err(
                                arm.span.clone(),
                                "pattern matching guards are not allowed in Hacspec",
                            );
                            return Err(());
                        }
                        let arm_body = translate_expr_expects_exp(sess, specials, &*arm.body)?;
                        // We only allow for a very specific type of pattern
                        let (enum_name, case_name, pat) = match &arm.pat.kind {
                            PatKind::Path(None, ast::Path { segments, .. }) => {
                                if segments.len() != 2 {
                                    sess.span_rustspec_err(
                                        ((arm.pat).span).clone(),
                                        "expected <name of the enum>::<name of the case>",
                                    );
                                    return Err(());
                                }
                                let mut it = segments.iter();
                                let first_seg = it.next().unwrap();
                                let second_seg = it.next().unwrap();
                                (
                                    BaseTyp::Named(
                                        translate_toplevel_ident(
                                            &first_seg.ident,
                                            TopLevelIdentKind::Type,
                                        ),
                                        match &first_seg.args {
                                            None => None,
                                            Some(args) => Some(translate_type_args(
                                                sess,
                                                args,
                                                &first_seg.ident.span,
                                            )?),
                                        },
                                    ),
                                    translate_toplevel_ident(
                                        &second_seg.ident,
                                        TopLevelIdentKind::EnumConstructor,
                                    ),
                                    None,
                                )
                            }
                            PatKind::TupleStruct(None, ast::Path { segments, .. }, args) => {
                                if segments.len() != 2 {
                                    sess.span_rustspec_err(
                                        ((arm.pat).span).clone(),
                                        "expected <name of the enum>::<name of the case>",
                                    );
                                    return Err(());
                                }
                                let mut it = segments.iter();
                                let first_seg = it.next().unwrap();
                                let second_seg = it.next().unwrap();
                                let pat_args = check_vec(
                                    args.iter()
                                        .map(|arg| translate_pattern(sess, arg))
                                        .collect(),
                                )?;
                                let pat = if pat_args.len() == 1 {
                                    pat_args.into_iter().next().unwrap()
                                } else {
                                    (Pattern::Tuple(pat_args), arm.pat.span.clone().into())
                                };
                                (
                                    BaseTyp::Named(
                                        translate_toplevel_ident(
                                            &first_seg.ident,
                                            TopLevelIdentKind::Type,
                                        ),
                                        match &first_seg.args {
                                            None => None,
                                            Some(args) => Some(translate_type_args(
                                                sess,
                                                args,
                                                &first_seg.ident.span,
                                            )?),
                                        },
                                    ),
                                    translate_toplevel_ident(
                                        &second_seg.ident,
                                        TopLevelIdentKind::EnumConstructor,
                                    ),
                                    Some(pat),
                                )
                            }
                            _ => {
                                sess.span_rustspec_err(
                                    ((arm.pat).span).clone(),
                                    "the only types of match pattern allowed in Hacspec start by \
                                <name of the enum>::<name of the case>",
                                );
                                return Err(());
                            }
                        };
                        Ok((enum_name, case_name, pat, arm_body))
                    })
                    .collect(),
            )?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::MatchWith(Box::new(e1), arms)),
                e.span.clone().into(),
            ))
        }
        ExprKind::Closure(_, _, _, _, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "closures are not allowed in Hacspec");
            Err(())
        }
        ExprKind::Block(block, _)
            if block.stmts.len() == 1 && block.rules == BlockCheckMode::Default =>
        {
            let translated_statements =
                translate_statement(sess, specials, block.stmts.iter().next().unwrap())?;
            match (
                translated_statements.len(),
                translated_statements.iter().next().unwrap(),
            ) {
                (1, (Statement::ReturnExp(e), span)) => {
                    Ok((ExprTranslationResult::TransExpr(e.clone()), span.clone()))
                }
                _ => {
                    sess.span_rustspec_err(
                        e.span.clone(),
                        "only inline block with a simple return expression are allowed in Hacspec",
                    );
                    Err(())
                }
            }
        }
        ExprKind::Block(_, _) => {
            sess.span_rustspec_err(e.span.clone(), "inline blocks are not allowed in Hacspec");
            Err(())
        }
        ExprKind::Async(_, _, _) => {
            sess.span_rustspec_err(e.span.clone(), "async/await is not allowed in Hacspec");
            Err(())
        }
        ExprKind::Await(_) => {
            sess.span_rustspec_err(e.span.clone(), "async/await is not allowed in Hacspec");
            Err(())
        }
        ExprKind::TryBlock(_) => {
            sess.span_rustspec_err(e.span.clone(), "try blocks are not allowed in Hacspec");
            Err(())
        }
        ExprKind::AssignOp(_, _, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "assignment operators are not supported yet in Hacspec",
            );
            Err(())
        }
        ExprKind::Field(_, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "struct field accesses are not supported yet in Hacspec",
            );
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
            let new_e1 = translate_expr_expects_exp(sess, specials, e1)?;
            let new_e2 = translate_expr_expects_exp(sess, specials, e2)?;
            Ok((
                ExprTranslationResult::TransExpr(Expression::Tuple(vec![new_e1, new_e2])),
                e.span.into(),
            ))
        }
        ExprKind::AddrOf(_, _, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "borrows outside function arguments are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Break(_, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "break statements are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Continue(_) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "continue statements are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Ret(_) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "early return statements are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::InlineAsm(_) => {
            sess.span_rustspec_err(e.span.clone(), "inline assembly is not allowed in Hacspec");
            Err(())
        }
        ExprKind::LlvmInlineAsm(_) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "inline LLVM assembly is not allowed in hacspec",
            );
            Err(())
        }
        ExprKind::MacCall(call) => {
            if call.path.segments.len() > 1 {
                sess.span_rustspec_err(
                    call.path.span,
                    "cannot use macros other than the ones defined by Hacspec",
                );
                return Err(());
            }
            let name = call.path.segments.first().unwrap();
            match (
                name.ident.name.to_ident_string().as_str(),
                name.args.as_ref(),
            ) {
                ("byte_seq", None) => match &*call.args {
                    MacArgs::Delimited(_, _, tokens) => {
                        let array = check_for_literal_array_from_macro_args(sess, &tokens)?;
                        return Ok((
                            (ExprTranslationResult::TransExpr(Expression::NewArray(
                                None,
                                None,
                                array
                                    .into_iter()
                                    .map(|i| {
                                        (
                                            Expression::FuncCall(
                                                None,
                                                (U8_TYP(), e.span.into()),
                                                vec![(
                                                    i.clone(),
                                                    (Borrowing::Consumed, i.1.clone()),
                                                )],
                                            ),
                                            i.1.clone(),
                                        )
                                    })
                                    .collect(),
                            ))),
                            e.span.into(),
                        ));
                    }
                    _ => {
                        sess.span_rustspec_err(
                            call.args.span().unwrap().clone(),
                            "expected parenthesis-delimited args",
                        );
                        return Err(());
                    }
                },
                ("public_byte_seq", None) => match &*call.args {
                    MacArgs::Delimited(_, _, tokens) => {
                        let array = check_for_literal_array_from_macro_args(sess, &tokens)?;
                        return Ok((
                            (ExprTranslationResult::TransExpr(Expression::NewArray(
                                None, None, array,
                            ))),
                            e.span.into(),
                        ));
                    }
                    _ => {
                        sess.span_rustspec_err(
                            call.args.span().unwrap().clone(),
                            "expected parenthesis-delimited args",
                        );
                        return Err(());
                    }
                },
                _ => {
                    sess.span_rustspec_err(
                        e.span.clone(),
                        "this macro call is not allowed in Hacspec",
                    );
                    Err(())
                }
            }
        }
        ExprKind::Repeat(_, _) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "repeat statements are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Yield(_) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "yield statements are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Paren(e1) => translate_expr(sess, specials, e1),
        ExprKind::Try(_) => {
            sess.span_rustspec_err(
                e.span.clone(),
                "question marks inside expressions are not allowed in Hacspec",
            );
            Err(())
        }
        ExprKind::Err => {
            sess.span_rustspec_err(e.span, "error expressions are not allowed in Hacspec");
            Err(())
        }
        ExprKind::ConstBlock(_) => {
            sess.span_rustspec_err(e.span.clone(), "const blocks are not allowed in Hacspec");
            Err(())
        }
        ExprKind::Underscore => {
            sess.span_rustspec_err(e.span.clone(), "underscores are not allowed in Hacspec");
            Err(())
        }
    }
}

enum ExprTranslationResultMaybeQuestionMark {
    TransExpr(Expression, bool), // true if ends with question mark
    TransStmt(Statement),
}

fn translate_expr_accepts_question_mark(
    sess: &Session,
    specials: &SpecialNames,
    e: &Expr,
) -> TranslationResult<Spanned<ExprTranslationResultMaybeQuestionMark>> {
    match &e.kind {
        ExprKind::Try(inner_e) => {
            let (result, span) = translate_expr(sess, specials, &inner_e)?;
            match result {
                ExprTranslationResult::TransExpr(e) => Ok((
                    ExprTranslationResultMaybeQuestionMark::TransExpr(e, true),
                    span,
                )),
                ExprTranslationResult::TransStmt(_) => {
                    sess.span_rustspec_err(
                        inner_e.span,
                        "question-marked blobs cannot contain statements \
                    in Hacspec, only pure expressions",
                    );
                    Err(())
                }
            }
        }
        _ => {
            let (result, span) = translate_expr(sess, specials, e)?;
            match result {
                ExprTranslationResult::TransExpr(e) => Ok((
                    ExprTranslationResultMaybeQuestionMark::TransExpr(e, false),
                    span,
                )),
                ExprTranslationResult::TransStmt(s) => {
                    Ok((ExprTranslationResultMaybeQuestionMark::TransStmt(s), span))
                }
            }
        }
    }
}

fn translate_pattern(sess: &Session, pat: &Pat) -> TranslationResult<Spanned<Pattern>> {
    match &pat.kind {
        PatKind::Ident(BindingMode::ByValue(_), id, None) => {
            Ok((Pattern::IdentPat(translate_ident(id).0), pat.span.into()))
        }
        PatKind::TupleStruct(None, path, args) => {
            let struct_name = translate_struct_name(sess, path)?;
            if args.len() == 1 {
                let arg = args.into_iter().next().unwrap();
                let new_arg = translate_pattern(sess, arg)?;
                Ok((
                    Pattern::SingleCaseEnum((struct_name, path.span.into()), Box::new(new_arg)),
                    pat.span.into(),
                ))
            } else {
                let new_args = check_vec(
                    args.into_iter()
                        .map(|arg| translate_pattern(sess, arg))
                        .collect(),
                )?;
                Ok((
                    Pattern::SingleCaseEnum(
                        (struct_name, path.span.into()),
                        Box::new((Pattern::Tuple(new_args), pat.span.into())),
                    ),
                    pat.span.into(),
                ))
            }
        }
        PatKind::Tuple(pats) => {
            let pats = pats
                .into_iter()
                .map(|pat| translate_pattern(sess, pat))
                .collect();
            let pats = check_vec(pats)?;
            Ok((Pattern::Tuple(pats), pat.span.into()))
        }
        PatKind::Wild => Ok((Pattern::WildCard, pat.span.into())),
        _ => {
            sess.span_rustspec_err(pat.span, "pattern not allowed in Hacspec let bindings");
            Err(())
        }
    }
}

fn translate_statement(
    sess: &Session,
    specials: &SpecialNames,
    s: &Stmt,
) -> TranslationResult<Vec<Spanned<Statement>>> {
    match &s.kind {
        StmtKind::Item(_) => {
            sess.span_rustspec_err(s.span, "block-local items are not allowed in Hacspec");
            Err(())
        }
        StmtKind::MacCall(_) => {
            sess.span_rustspec_err(
                s.span,
                "macro calls inside code blocks are not allowed inside Hacspec",
            );
            Err(())
        }
        StmtKind::Empty => {
            sess.span_rustspec_err(s.span, "empty blocks are not allowed in Hacspec");
            Err(())
        }
        StmtKind::Local(local) => {
            let pat = translate_pattern(sess, &local.pat)?;
            let ty: Option<Spanned<Typ>> = match local.ty.clone() {
                None => None,
                Some(ty) => Some(translate_typ(sess, &ty)?),
            };
            let (init, question_mark) = match &local.kind {
                LocalKind::Decl | LocalKind::InitElse(_, _) => {
                    sess.span_rustspec_err(
                        local.span,
                        "let-bindings without initialization are not allowed in Hacspec",
                    );
                    Err(())
                }
                LocalKind::Init(e) => {
                    match translate_expr_accepts_question_mark(sess, specials, &e)? {
                        (ExprTranslationResultMaybeQuestionMark::TransStmt(_), _) => {
                            sess.span_rustspec_err(
                                e.span,
                                "let binding expression should not contain statements in Hacspec",
                            );
                            Err(())
                        }
                        (
                            ExprTranslationResultMaybeQuestionMark::TransExpr(e, question_mark),
                            span,
                        ) => Ok(((e, span), question_mark)),
                    }
                }
            }?;
            Ok(vec![(
                Statement::LetBinding(pat, ty, init, question_mark),
                s.span.into(),
            )])
        }
        StmtKind::Expr(e) => {
            let t_s = match translate_expr(sess, specials, &e)? {
                (ExprTranslationResult::TransExpr(e), _) => Statement::ReturnExp(e),
                (ExprTranslationResult::TransStmt(s), _) => s,
            };
            Ok(vec![(t_s, s.span.into())])
        }
        StmtKind::Semi(e) => {
            let t_s = match translate_expr_accepts_question_mark(sess, specials, &e)? {
                (ExprTranslationResultMaybeQuestionMark::TransExpr(e, question_mark), span) => {
                    Statement::LetBinding((Pattern::WildCard, span), None, (e, span), question_mark)
                }
                (ExprTranslationResultMaybeQuestionMark::TransStmt(s), _) => s,
            };
            Ok(vec![(t_s, s.span.into())])
        }
    }
}

fn translate_block(
    sess: &Session,
    specials: &SpecialNames,
    b: &ast::Block,
) -> TranslationResult<Spanned<Block>> {
    match b.rules {
        BlockCheckMode::Unsafe(_) => {
            sess.span_rustspec_err(b.span, "unsafe blocks are not allowed in Hacspec");
            return Err(());
        }
        BlockCheckMode::Default => (),
    };
    let stmts = b
        .stmts
        .iter()
        .map(|s| translate_statement(sess, specials, &s))
        .collect();
    let stmts = check_vec(stmts)?.into_iter().flatten().collect();
    Ok((
        Block {
            stmts,
            return_typ: None,
            mutated: None,
            contains_question_mark: None,
            // We initialize these fields to None as they are
            // to be filled by the typechecker
        },
        b.span.into(),
    ))
}

enum ItemTranslationResult {
    Item(DecoratedItem),
    Ignored,
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

fn check_for_literal(sess: &Session, arg: &TokenTree) -> TranslationResult<Spanned<Expression>> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Literal(l) => {
                match translate_literal(
                    sess,
                    &match rustc_ast::Lit::from_lit_token(l, tok.span.clone()) {
                        Ok(x) => x,
                        Err(_) => return Err(()),
                    },
                    tok.span.clone(),
                )? {
                    (ExprTranslationResult::TransStmt(_), _) => panic!(), // should not happen
                    (ExprTranslationResult::TransExpr(e), s) => Ok((e, s)),
                }
            }
            _ => {
                sess.span_rustspec_err(tok.span.clone(), "expected a literal");
                Err(())
            }
        },
        _ => {
            sess.span_rustspec_err(arg.span().clone(), "expected a literal");
            Err(())
        }
    }
}

fn check_for_literal_array_from_macro_args(
    sess: &Session,
    inside: &TokenStream,
) -> TranslationResult<Vec<Spanned<Expression>>> {
    let commas_and_exprs: Vec<TranslationResult<Option<Spanned<Expression>>>> = inside
        .trees()
        .enumerate()
        .map(|(i, tok)| {
            if i % 2 == 1 {
                check_for_comma(sess, &tok)?;
                Ok(None)
            } else {
                Ok(Some(check_for_literal(sess, &tok)?))
            }
        })
        .collect();
    let commas_and_exprs = check_vec(commas_and_exprs)?;
    Ok(commas_and_exprs.into_iter().filter_map(|x| x).collect())
}

fn check_for_literal_array(
    sess: &Session,
    arg: &TokenTree,
) -> TranslationResult<Vec<Spanned<Expression>>> {
    match arg {
        TokenTree::Delimited(_, DelimToken::Bracket, inside) => {
            let commas_and_exprs: Vec<TranslationResult<Option<Spanned<Expression>>>> = inside
                .trees()
                .enumerate()
                .map(|(i, tok)| {
                    if i % 2 == 1 {
                        check_for_comma(sess, &tok)?;
                        Ok(None)
                    } else {
                        Ok(Some(check_for_literal(sess, &tok)?))
                    }
                })
                .collect();
            let commas_and_exprs = check_vec(commas_and_exprs)?;
            Ok(commas_and_exprs.into_iter().filter_map(|x| x).collect())
        }
        _ => {
            sess.span_rustspec_err(
                arg.span().clone(),
                "expected delimiter to be a bracket-enclosed expression",
            );
            Err(())
        }
    }
}

fn check_for_colon(sess: &Session, arg: &TokenTree) -> TranslationResult<()> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Colon => Ok(()),
            _ => {
                sess.span_rustspec_err(tok.span.clone(), "expected a colon");
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
                        Ok(x) => Ok((Expression::Lit(Literal::Usize(x)), tok.span.clone().into())),
                    },
                },
                _ => {
                    sess.span_rustspec_err(tok.span.clone(), "expected an integer");
                    Err(())
                }
            },
            TokenKind::Ident(name, _) => Ok((
                Expression::Named(Ident::Unresolved(name.to_ident_string())),
                tok.span.clone().into(),
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

fn check_for_toplevel_ident(
    sess: &Session,
    arg: &TokenTree,
    kind: TopLevelIdentKind,
) -> TranslationResult<(Spanned<TopLevelIdent>, String)> {
    match arg {
        TokenTree::Token(tok) => match tok.kind {
            TokenKind::Ident(id, _) => Ok((
                (
                    TopLevelIdent {
                        string: id.to_ident_string(),
                        kind,
                    },
                    tok.span.clone().into(),
                ),
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

fn translate_simplified_natural_integer_decl(
    sess: &Session,
    i: &ast::Item,
    specials: &SpecialNames,
    call: &MacCall,
    secrecy: Secrecy,
) -> TranslationResult<(ItemTranslationResult, SpecialNames)> {
    match &*call.args {
        MacArgs::Delimited(_, _, tokens) => {
            let mut it = tokens.trees();
            let (first_arg, second_arg, third_arg) = {
                let first_arg = it.next().map_or(Err(()), |x| Ok(x));
                let second_arg = it.next().map_or(Err(()), |x| Ok(x));
                let third_arg = it.next().map_or(Err(()), |x| Ok(x));
                Ok((first_arg?, second_arg?, third_arg?))
            }?;
            let (typ_ident, typ_ident_string) =
                check_for_toplevel_ident(sess, &first_arg, TopLevelIdentKind::Type)?;
            check_for_comma(sess, &second_arg)?;
            let canvas_size = check_for_usize(sess, &third_arg)?;
            Ok((
                (ItemTranslationResult::Item(DecoratedItem {
                    item: Item::NaturalIntegerDecl(typ_ident, secrecy, canvas_size, None),
                    tags: ItemTagSet(HashSet::unit("code".to_string())),
                })),
                SpecialNames {
                    arrays: specials.arrays.update(typ_ident_string),
                    ..specials.clone()
                },
            ))
        }
        _ => {
            sess.span_rustspec_err(i.span.clone(), "expected delimited macro arguments");
            Err(())
        }
    }
}

fn translate_natural_integer_decl(
    sess: &Session,
    i: &ast::Item,
    specials: &SpecialNames,
    call: &MacCall,
    secrecy: Secrecy,
) -> TranslationResult<(ItemTranslationResult, SpecialNames)> {
    match &*call.args {
        MacArgs::Delimited(_, _, tokens) => {
            let mut it = tokens.trees();
            let (
                first_arg,
                second_arg,
                third_arg,
                fourth_arg,
                fifth_arg,
                sixth_arg,
                seventh_arg,
                eight_arg,
                ninth_arg,
                tenth_arg,
                eleventh_arg,
                twelveth_arg,
                thirteenth_arg,
                fourteenth_arg,
                fiftheen_arg,
            ) = {
                let first_arg = it.next().map_or(Err(()), |x| Ok(x));
                let second_arg = it.next().map_or(Err(()), |x| Ok(x));
                let third_arg = it.next().map_or(Err(()), |x| Ok(x));
                let fourth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let fifth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let sixth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let seventh_arg = it.next().map_or(Err(()), |x| Ok(x));
                let eight_arg = it.next().map_or(Err(()), |x| Ok(x));
                let ninth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let tenth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let eleventh_arg = it.next().map_or(Err(()), |x| Ok(x));
                let twelveth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let thirteenth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let fourteenth_arg = it.next().map_or(Err(()), |x| Ok(x));
                let fiftheen_arg = it.next().map_or(Err(()), |x| Ok(x));
                Ok((
                    first_arg?,
                    second_arg?,
                    third_arg?,
                    fourth_arg?,
                    fifth_arg?,
                    sixth_arg?,
                    seventh_arg?,
                    eight_arg?,
                    ninth_arg?,
                    tenth_arg?,
                    eleventh_arg?,
                    twelveth_arg?,
                    thirteenth_arg?,
                    fourteenth_arg?,
                    fiftheen_arg?,
                ))
            }?;
            check_for_toplevel_ident(sess, &first_arg, TopLevelIdentKind::Function)?;
            check_for_colon(sess, &second_arg)?;
            let (typ_ident, typ_ident_string) =
                check_for_toplevel_ident(sess, &third_arg, TopLevelIdentKind::Type)?;
            check_for_comma(sess, &fourth_arg)?;
            check_for_toplevel_ident(sess, &fifth_arg, TopLevelIdentKind::Function)?;
            check_for_colon(sess, &sixth_arg)?;
            let (canvas_typ_ident, _) =
                check_for_toplevel_ident(sess, &seventh_arg, TopLevelIdentKind::Type)?;
            check_for_comma(sess, &eight_arg)?;
            check_for_toplevel_ident(sess, &ninth_arg, TopLevelIdentKind::Function)?;
            check_for_colon(sess, &tenth_arg)?;
            let canvas_size = check_for_usize(sess, &eleventh_arg)?;
            check_for_comma(sess, &twelveth_arg)?;
            check_for_toplevel_ident(sess, &thirteenth_arg, TopLevelIdentKind::Function)?;
            check_for_colon(sess, &fourteenth_arg)?;
            let modulo_string = match &fiftheen_arg {
                TokenTree::Token(tok) => match tok.kind {
                    TokenKind::Literal(lit) => match lit.kind {
                        TokenLitKind::Str => (
                            lit.symbol.to_ident_string(),
                            seventh_arg.span().clone().into(),
                        ),
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
                (ItemTranslationResult::Item(DecoratedItem {
                    item: Item::NaturalIntegerDecl(
                        typ_ident,
                        secrecy,
                        canvas_size,
                        Some((canvas_typ_ident, modulo_string)),
                    ),
                    tags: ItemTagSet(HashSet::unit("code".to_string())),
                })),
                SpecialNames {
                    arrays: specials.arrays.update(typ_ident_string),
                    ..specials.clone()
                },
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
    specials: &SpecialNames,
    call: &MacCall,
    cell_t: Option<BaseTyp>,
) -> TranslationResult<(ItemTranslationResult, SpecialNames)> {
    match &*call.args {
        MacArgs::Delimited(_, _, tokens) => {
            let mut it = tokens.trees();
            let (first_arg, second_arg, third_arg) = {
                let first_arg = it.next().map_or(Err(()), |x| Ok(x));
                let second_arg = it.next().map_or(Err(()), |x| Ok(x));
                let third_arg = it.next().map_or(Err(()), |x| Ok(x));
                Ok((first_arg?, second_arg?, third_arg?))
            }?;
            let (typ_ident, typ_ident_string) =
                check_for_toplevel_ident(sess, &first_arg, TopLevelIdentKind::Type)?;
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
                                    tokens: None,
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
            let index_typ = {
                let (fourth_arg, fifth_arg, sixth_arg, seventh_arg) = {
                    let fourth_arg = it.next();
                    let fifth_arg = it.next();
                    let sixth_arg = it.next();
                    let seventh_arg = it.next();
                    (fourth_arg, fifth_arg, sixth_arg, seventh_arg)
                };
                match (fourth_arg, fifth_arg, sixth_arg, seventh_arg) {
                    (Some(fourth_arg), Some(fifth_arg), Some(sixth_arg), Some(seventh_arg)) => {
                        check_for_comma(sess, &fourth_arg)?;
                        check_for_toplevel_ident(sess, &fifth_arg, TopLevelIdentKind::Type)?;
                        check_for_colon(sess, &sixth_arg)?;
                        match seventh_arg {
                            TokenTree::Token(tok) => match tok.kind {
                                TokenKind::Ident(id, _) => Some((
                                    TopLevelIdent {
                                        string: id.to_ident_string(),
                                        kind: TopLevelIdentKind::Type,
                                    },
                                    tok.span.clone().into(),
                                )),
                                _ => {
                                    sess.span_rustspec_err(
                                        tok.span.clone(),
                                        "expected an identifier",
                                    );
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
                        }
                    }
                    _ => None,
                }
            };
            Ok((
                (ItemTranslationResult::Item(DecoratedItem {
                    item: Item::ArrayDecl(typ_ident, size, cell_t, index_typ),
                    tags: ItemTagSet(HashSet::unit("code".to_string())),
                })),
                SpecialNames {
                    arrays: specials.arrays.update(typ_ident_string),
                    ..specials.clone()
                },
            ))
        }
        _ => {
            sess.span_rustspec_err(i.span.clone(), "expected delimited macro arguments");
            Err(())
        }
    }
}

fn attribute_is_test(attr: &Attribute) -> bool {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "test" => true,
        "cfg" => {
            let inner_tokens = attr.tokens().to_tokenstream();
            if inner_tokens.len() != 2 {
                return false;
            }
            let mut it = inner_tokens.trees();
            let first_token = it.next().unwrap();
            let second_token = it.next().unwrap();
            match (first_token, second_token) {
                (TokenTree::Token(first_tok), TokenTree::Delimited(_, _, inner)) => {
                    match first_tok.kind {
                        TokenKind::Pound => {
                            if inner.len() != 2 {
                                return false;
                            }
                            let mut it = inner.trees();
                            let _first_token = it.next().unwrap();
                            // First is cfg
                            let second_token = it.next().unwrap();
                            match second_token {
                                TokenTree::Delimited(_, _, inner) => {
                                    if inner.len() != 1 {
                                        return false;
                                    }
                                    let mut it = inner.trees();
                                    let first_token = it.next().unwrap();
                                    match first_token {
                                        TokenTree::Token(tok) => match tok.kind {
                                            TokenKind::Ident(ident, _) => {
                                                ident.to_ident_string() == "test"
                                            }
                                            _ => false,
                                        },
                                        _ => false,
                                    }
                                }
                                _ => false,
                            }
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn attribute_tag(attr: &Attribute) -> Option<Vec<ItemTag>> {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "quickcheck" | "test" => Some(vec![attr_name]),
        "derive" => {
            let inner_tokens = attr.tokens().to_tokenstream();
            if inner_tokens.len() != 2 {
                return None;
            }
            let mut it = inner_tokens.trees();
            let first_token = it.next().unwrap();
            let second_token = it.next().unwrap();
            match (first_token, second_token) {
                (TokenTree::Token(first_tok), TokenTree::Delimited(_, _, inner)) => {
                    match first_tok.kind {
                        TokenKind::Pound => {
                            if inner.len() != 2 {
                                return None;
                            }
                            let mut it = inner.trees();
                            let _first_token = it.next().unwrap();
                            // First is derive
                            let second_token = it.next().unwrap();
                            match second_token {
                                TokenTree::Delimited(_, _, inner) => {
                                    Some(inner.trees().fold(Vec::new(), |mut a, x| match x {
                                        TokenTree::Token(tok) => match tok.kind {
                                            TokenKind::Ident(ident, _) => {
                                                a.push(ident.to_ident_string());
                                                a
                                            }
                                            _ => a,
                                        },
                                        _ => a,
                                    }))
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        "cfg" => {
            let inner_tokens = attr.tokens().to_tokenstream();
            if inner_tokens.len() != 2 {
                return None;
            }
            let mut it = inner_tokens.trees();
            let first_token = it.next().unwrap();
            let second_token = it.next().unwrap();
            match (first_token, second_token) {
                (TokenTree::Token(first_tok), TokenTree::Delimited(_, _, inner)) => {
                    match first_tok.kind {
                        TokenKind::Pound => {
                            if inner.len() != 2 {
                                return None;
                            }
                            let mut it = inner.trees();
                            let _first_token = it.next().unwrap();
                            // First is cfg
                            let second_token = it.next().unwrap();
                            match second_token {
                                TokenTree::Delimited(_, _, inner) => {
                                    if inner.len() != 1 {
                                        return None;
                                    }
                                    let mut it = inner.trees();
                                    let first_token = it.next().unwrap();
                                    match first_token {
                                        TokenTree::Token(tok) => match tok.kind {
                                            TokenKind::Ident(ident, _) => {
                                                let ident_string = ident.to_ident_string();
                                                match ident_string.as_str() {
                                                    "proof" | "test" => Some(vec![ident_string]),
                                                    _ => None,
                                                }
                                            }
                                            _ => None,
                                        },
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        // "test" => true, // proof
        _ => None,
    }
}

fn translate_items<F: Fn(&Vec<Spanned<String>>) -> ExternalData>(
    sess: &Session,
    i: &ast::Item,
    specials: &SpecialNames,
    external_data: &F,
) -> TranslationResult<(ItemTranslationResult, SpecialNames)> {
    let mut tags = HashSet::new();
    tags.insert("code".to_string());
    let export = i
        .attrs
        .iter()
        .fold(false, |b, attr| match attribute_tag(attr) {
            Some(a) => {
                tags.extend(a.iter());
                b || a.contains(&"proof".to_string())
            }
            None => b,
        });

    if i.attrs.iter().any(attribute_is_test) && !export {
        return Ok((ItemTranslationResult::Ignored, specials.clone()));
    }
    match &i.kind {
        ItemKind::Fn(fn_kind) => {
            // Foremost we check whether this function is a test, in which case
            // we ignore it
            let FnKind {
                defaultness,
                ref sig,
                ref generics,
                ref body,
            } = fn_kind.as_ref();
            // First, checking that no fancy function qualifier is here
            match defaultness {
                Defaultness::Default(span) => {
                    sess.span_rustspec_err(
                        span.clone(),
                        "\"default\" keyword not allowed in Hacspec",
                    );
                    return Err(());
                }
                _ => (),
            }
            match sig.header.unsafety {
                Unsafe::No => (),
                Unsafe::Yes(span) => {
                    sess.span_rustspec_err(span.clone(), "unsafe functions not allowed in Hacspec");
                    return Err(());
                }
            }
            match sig.header.asyncness {
                Async::No => (),
                Async::Yes { span, .. } => {
                    sess.span_rustspec_err(span.clone(), "async functions not allowed in Hacspec");
                    return Err(());
                }
            }
            match sig.header.constness {
                Const::No => (),
                Const::Yes(span) => {
                    sess.span_rustspec_err(span.clone(), "const functions not allowed in Hacspec");
                    return Err(());
                }
            }
            match sig.header.ext {
                Extern::None => (),
                _ => {
                    sess.span_rustspec_err(
                        i.span.clone(),
                        "extern functions not allowed in Hacspec",
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
                        PatKind::Ident(BindingMode::ByValue(_), id, None) => {
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
                            "pattern destructuring in function arguments not allowed in Hacspec",
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
                    "generics are not allowed in Hacspec",
                );
                return Err(());
            };
            let fn_inputs = check_vec(fn_inputs)?;
            let fn_output = match &sig.decl.output {
                FnRetTy::Default(span) => (BaseTyp::Unit, span.clone().into()),
                FnRetTy::Ty(ty) => translate_base_typ(sess, ty)?,
            };
            let fn_body: Spanned<Block> = match body {
                None => (
                    Block {
                        stmts: Vec::new(),
                        return_typ: None,
                        mutated: None,
                        contains_question_mark: None,
                    },
                    i.span.into(),
                ),
                Some(b) => translate_block(sess, specials, &b)?,
            };
            let fn_sig = FuncSig {
                args: fn_inputs,
                ret: fn_output,
            };
            let fn_item = Item::FnDecl(
                translate_toplevel_ident(&i.ident, TopLevelIdentKind::Function),
                fn_sig,
                fn_body,
            );

            Ok((
                ItemTranslationResult::Item(DecoratedItem {
                    item: fn_item,
                    tags: ItemTagSet(tags),
                }),
                specials.clone(),
            ))
        }
        ItemKind::Use(ref tree) => match tree.kind {
            UseTreeKind::Glob => {
                let krate_name = translate_use_path(sess, &tree.prefix)?;
                let data = external_data(&vec![(krate_name.clone(), i.span.into())]);
                let mut specials = specials.clone();
                for (enum_name, _) in data.enums.into_iter() {
                    specials.enums.insert(enum_name);
                }
                for (alias_name, alias_ty) in data.ty_aliases.into_iter() {
                    specials.aliases.insert(alias_name, alias_ty);
                }
                Ok((
                    ItemTranslationResult::Item(DecoratedItem {
                        item: Item::ImportedCrate((
                            TopLevelIdent {
                                string: krate_name,
                                kind: TopLevelIdentKind::Crate,
                            },
                            tree.span.clone().into(),
                        )),
                        tags: ItemTagSet(tags),
                    }),
                    specials,
                ))
            }
            _ => {
                sess.span_rustspec_err(tree.span.clone(), "only ::* uses are allowed in Hacspec");
                Err(())
            }
        },
        ItemKind::MacCall(call) => {
            if call.path.segments.len() > 1 {
                sess.span_rustspec_err(
                    call.path.span,
                    "cannot use macros other than the ones defined by Hacspec",
                );
                return Err(());
            }
            let name = call.path.segments.first().unwrap();
            match (
                name.ident.name.to_ident_string().as_str(),
                name.args.as_ref(),
            ) {
                ("array", None) => translate_array_decl(sess, i, specials, call, None),
                ("bytes", None) => translate_array_decl(
                    sess,
                    i,
                    specials,
                    call,
                    Some(BaseTyp::Named((U8_TYP(), i.span.clone().into()), None)),
                ),
                ("public_bytes", None) => {
                    translate_array_decl(sess, i, specials, call, Some(BaseTyp::UInt8))
                }
                ("public_nat_mod", None) => {
                    translate_natural_integer_decl(sess, i, specials, call, Secrecy::Public)
                }
                ("nat_mod", None) => {
                    translate_natural_integer_decl(sess, i, specials, call, Secrecy::Secret)
                }
                ("unsigned_public_integer", None) => translate_simplified_natural_integer_decl(
                    sess,
                    i,
                    specials,
                    call,
                    Secrecy::Public,
                ),
                (_, None) => {
                    sess.span_rustspec_err(name.ident.span.clone(), "unknown Hacspec macro");
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
            let new_e = translate_expr_expects_exp(sess, specials, e)?;
            let id = translate_toplevel_ident(&i.ident, TopLevelIdentKind::Constant);
            Ok((
                ItemTranslationResult::Item(DecoratedItem {
                    item: Item::ConstDecl(id, new_ty, new_e),
                    tags: ItemTagSet(tags),
                }),
                specials.clone(),
            ))
        }
        ItemKind::Const(_, _, None) => {
            sess.span_rustspec_err(
                i.span.clone(),
                "uninitialized consts not allowed in Hacspec",
            );
            Err(())
        }
        ItemKind::TyAlias(ty_alias_kind) => {
            let TyAliasKind {
                defaultness,
                generics,
                ty,
                ..
            } = ty_alias_kind.as_ref();
            match defaultness {
                Defaultness::Final => (),
                Defaultness::Default(span) => {
                    sess.span_rustspec_err(
                        span.clone(),
                        "default type aliases not supported in Hacspec",
                    );
                    return Err(());
                }
            };
            if generics.params.len() > 0 {
                sess.span_rustspec_err(
                    generics.span.clone(),
                    "generics in type aliases not supported in Hacspec",
                );
                return Err(());
            }
            match ty {
                None => {
                    sess.span_rustspec_err(
                        generics.span.clone(),
                        "type aliases should have a definition in Hacspec",
                    );
                    Err(())
                }
                Some(ty) => {
                    let ty = translate_base_typ(sess, ty)?;
                    let mut specials = specials.clone();
                    let ty_alias_name_string = i.ident.name.to_ident_string();
                    specials
                        .aliases
                        .insert(ty_alias_name_string.clone(), ty.0.clone());
                    let ty_alias_name = (
                        TopLevelIdent {
                            string: ty_alias_name_string,
                            kind: TopLevelIdentKind::Type,
                        },
                        i.span.into(),
                    );
                    Ok((
                        ItemTranslationResult::Item(DecoratedItem {
                            item: Item::AliasDecl(ty_alias_name, ty),
                            tags: ItemTagSet(tags),
                        }),
                        specials,
                    ))
                }
            }
        }
        ItemKind::ExternCrate(_) => {
            sess.span_rustspec_err(
                i.span.clone(),
                "external crate declarations not allowed in Hacspec",
            );
            Err(())
        }
        ItemKind::Static(_, _, _) => {
            sess.span_rustspec_err(i.span.clone(), "static items not allowed in Hacspec");
            Err(())
        }
        ItemKind::Mod(_, _) => {
            sess.span_rustspec_err(i.span.clone(), "sub-modules not allowed in Hacspec");
            Err(())
        }
        ItemKind::ForeignMod(_) => {
            sess.span_rustspec_err(i.span.clone(), "foreign modules not allowed in Hacspec");
            Err(())
        }
        ItemKind::GlobalAsm(_) => {
            sess.span_rustspec_err(i.span.clone(), "assembly globals not allowed in Hacspec");
            Err(())
        }
        ItemKind::Enum(def, generics) => {
            if generics.params.len() > 0 {
                sess.span_rustspec_err(
                    generics.span.clone(),
                    "type parameters in enum declarations forbidden in Hacspec",
                );
                return Err(());
            }
            let id_string = i.ident.name.to_ident_string();
            let id = translate_toplevel_ident(&i.ident, TopLevelIdentKind::Type);
            let variants = check_vec(
                def.variants
                    .iter()
                    .map(|v| {
                        let case_id =
                            translate_toplevel_ident(&v.ident, TopLevelIdentKind::EnumConstructor);
                        let case_typ = match &v.data {
                            VariantData::Unit(_) => Ok(None),
                            VariantData::Struct(_, _) => {
                                sess.span_rustspec_err(
                                    v.span.clone(),
                                    "struct enum variants not allowed in Hacspec",
                                );
                                Err(())
                            }
                            VariantData::Tuple(args, _) => {
                                if args.len() == 1 {
                                    let arg = args.iter().next().unwrap();
                                    let arg_ty = translate_base_typ(sess, &arg.ty)?;
                                    Ok(Some(arg_ty))
                                } else {
                                    let args_ty = check_vec(
                                        args.iter()
                                            .map(|arg| translate_base_typ(sess, &*arg.ty))
                                            .collect(),
                                    )?;
                                    Ok(Some((BaseTyp::Tuple(args_ty), v.span.clone().into())))
                                }
                            }
                        };
                        Ok((case_id, case_typ?))
                    })
                    .collect(),
            )?;
            Ok((
                ItemTranslationResult::Item(DecoratedItem {
                    item: Item::EnumDecl(id, variants),
                    tags: ItemTagSet(tags),
                }),
                SpecialNames {
                    enums: specials.enums.update(id_string),
                    ..specials.clone()
                },
            ))
        }
        ItemKind::Struct(data, generics) => {
            if generics.params.len() > 0 {
                sess.span_rustspec_err(
                    generics.span.clone(),
                    "struct type parameters forbidden in Hacspec",
                );
                return Err(());
            }
            let id_string = i.ident.name.to_ident_string();
            let id = translate_toplevel_ident(&i.ident, TopLevelIdentKind::Type);
            match data {
                VariantData::Struct(_, _) => {
                    sess.span_rustspec_err(
                        i.span.clone(),
                        "structs with fields are forbidden in Hacspec",
                    );
                    Err(())
                }
                VariantData::Unit(_) => Ok((
                    ItemTranslationResult::Item(DecoratedItem {
                        item: Item::EnumDecl(
                            id.clone(),
                            vec![(
                                (
                                    TopLevelIdent {
                                        string: id.0.string,
                                        kind: TopLevelIdentKind::EnumConstructor,
                                    },
                                    id.1,
                                ),
                                None,
                            )],
                        ),
                        tags: ItemTagSet(tags),
                    }),
                    SpecialNames {
                        enums: specials.enums.update(id_string),
                        ..specials.clone()
                    },
                )),
                VariantData::Tuple(fields, _) => {
                    let tuple_args = check_vec(
                        fields
                            .into_iter()
                            .map(|field| match field.ident {
                                None => translate_base_typ(sess, &*field.ty),
                                Some(_) => {
                                    sess.span_rustspec_err(
                                        field.span.clone(),
                                        "structs fields cannot be named in Hacspec",
                                    );
                                    Err(())
                                }
                            })
                            .collect(),
                    )?;
                    let payload = if tuple_args.len() > 1 {
                        (BaseTyp::Tuple(tuple_args), i.span.clone().into())
                    } else {
                        tuple_args.into_iter().next().unwrap()
                    };
                    Ok((
                        ItemTranslationResult::Item(DecoratedItem {
                            item: Item::EnumDecl(
                                id.clone(),
                                vec![(
                                    (
                                        TopLevelIdent {
                                            string: id.0.string,
                                            kind: TopLevelIdentKind::EnumConstructor,
                                        },
                                        id.1,
                                    ),
                                    Some(payload),
                                )],
                            ),
                            tags: ItemTagSet(tags),
                        }),
                        SpecialNames {
                            enums: specials.enums.update(id_string),
                            ..specials.clone()
                        },
                    ))
                }
            }
        }
        ItemKind::Union(_, _) => {
            sess.span_rustspec_err(i.span.clone(), "union declarations not allowed in Hacspec");
            Err(())
        }
        ItemKind::Trait(_) => {
            sess.span_rustspec_err(i.span.clone(), "trait declarations not allowed in Hacspec");
            Err(())
        }
        ItemKind::TraitAlias(_, _) => {
            sess.span_rustspec_err(i.span.clone(), "trait aliases not allowed in Hacspec");
            Err(())
        }
        ItemKind::Impl(_) => {
            sess.span_rustspec_err(i.span.clone(), "impl blocks not allowed in Hacspec");
            Err(())
        }
        ItemKind::MacroDef(_) => {
            sess.span_rustspec_err(i.span.clone(), "macro definitions not allowed in Hacspec");
            Err(())
        }
    }
}

pub fn translate<F: Fn(&Vec<Spanned<String>>) -> ExternalData>(
    sess: &Session,
    krate: &Crate,
    external_data: &F,
    specials: &mut SpecialNames,
) -> TranslationResult<Program> {
    let items = &krate.items;
    let translated_items = check_vec(
        items
            .into_iter()
            .map(|i| {
                let (new_i, new_specials) = translate_items(sess, &i, &specials, external_data)?;
                *specials = new_specials;
                Ok((new_i, i.span))
            })
            .collect(),
    )?;

    let items: Vec<_> = translated_items
        .into_iter()
        .filter(|(r, _)| match r {
            ItemTranslationResult::Item(_) => true,
            _ => false,
        })
        .collect();
    let items = items
        .into_iter()
        .map(|(r, r_span)| {
            match r {
                ItemTranslationResult::Item(i) => (i, r_span.into()),
                _ => panic!(), // should not happen
            }
        })
        .collect();

    Ok(Program { items })
}
