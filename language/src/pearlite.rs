use crate::ast_to_rustspec::{translate_base_typ, translate_expr_expects_exp, SpecialNames};
use crate::name_resolution::TopLevelContext;
use crate::rustspec::*;
use pretty::RcDoc;
use proc_macro2;
use rustc_ast::{
    ast::{self, AttrVec, Attribute, Expr, ExprKind, Path, PathSegment, Ty},
    node_id::NodeId,
    ptr::P,
    token::{Delimiter, Lit, LitKind as TokenLitKind, TokenKind},
    tokenstream::{TokenStream, TokenTree},
};
use rustc_session::Session;
use rustc_span::{symbol, Span};
use serde::{ser::SerializeSeq, Serialize, Serializer};

fn translate_pearlite_binop(op: syn::BinOp) -> ast::BinOpKind {
    match op {
        syn::BinOp::Add(_) => ast::BinOpKind::Add,
        syn::BinOp::Sub(_) => ast::BinOpKind::Sub,
        syn::BinOp::Mul(_) => ast::BinOpKind::Mul,
        syn::BinOp::Div(_) => ast::BinOpKind::Div,
        syn::BinOp::Rem(_) => ast::BinOpKind::Rem,
        syn::BinOp::And(_) => ast::BinOpKind::And,
        syn::BinOp::Or(_) => ast::BinOpKind::Or,
        syn::BinOp::BitXor(_) => ast::BinOpKind::BitXor,
        syn::BinOp::BitAnd(_) => ast::BinOpKind::BitAnd,
        syn::BinOp::BitOr(_) => ast::BinOpKind::BitOr,
        syn::BinOp::Shl(_) => ast::BinOpKind::Shl,
        syn::BinOp::Shr(_) => ast::BinOpKind::Shr,
        syn::BinOp::Eq(_) => ast::BinOpKind::Eq,
        syn::BinOp::Lt(_) => ast::BinOpKind::Lt,
        syn::BinOp::Le(_) => ast::BinOpKind::Le,
        syn::BinOp::Ne(_) => ast::BinOpKind::Ne,
        syn::BinOp::Ge(_) => ast::BinOpKind::Ge,
        syn::BinOp::Gt(_) => ast::BinOpKind::Gt,
        binop => panic!("binop error: {:#?}", binop), // Error
        // syn::BinOp::AddEq(_) => ast::BinOpKind::AddEq,
        // syn::BinOp::SubEq(_) => ast::BinOpKind::SubEq,
        // syn::BinOp::MulEq(_) => ast::BinOpKind::MulEq,
        // syn::BinOp::DivEq(_) => ast::BinOpKind::DivEq,
        // syn::BinOp::RemEq(_) => ast::BinOpKind::RemEq,
        // syn::BinOp::BitXorEq(_) => ast::BinOpKind::BitXorEq,
        // syn::BinOp::BitAndEq(_) => ast::BinOpKind::BitAndEq,
        // syn::BinOp::BitOrEq(_) => ast::BinOpKind::BitOrEq,
        // syn::BinOp::ShlEq(_) => ast::BinOpKind::ShlEq,
        // syn::BinOp::ShrEq(_) => ast::BinOpKind::ShrEq,
        // _ => RcDoc::as_string(format!("TODO: {:?}", b)),
    }
}

pub(crate) fn translate_pearlite_ident(
    ident: proc_macro2::Ident,
    span: Span,
) -> rustc_span::symbol::Ident {
    rustc_span::symbol::Ident::new(
        rustc_span::symbol::Symbol::intern(format!("{}", ident).as_str()),
        span, // translate_pearlite_span(ident.span())
    )
}

pub(crate) fn translate_pearlite_unquantified(
    sess: &Session,
    t: pearlite_syn::term::Term,
    span: Span,
) -> Option<Expr> {
    match translate_pearlite(sess, t, span) {
        Quantified::Unquantified(e) => Some(e),
        _ => None,
    }
}

fn translate_pearlite_lit<'a>(l: syn::Lit, span: Span) -> Lit {
    match l.clone() {
        syn::Lit::Int(lit) => {
            Lit {
                kind: rustc_ast::token::LitKind::Integer,
                symbol: rustc_span::symbol::Symbol::intern(lit.base10_digits()), // .value()
                suffix: Some(rustc_span::symbol::Symbol::intern(lit.suffix())), // None, // rustc_span::symbol::Symbol::intern(lit.suffix())
            }
        }
        syn::Lit::Bool(lit) => {
            Lit {
                kind: rustc_ast::token::LitKind::Bool,
                symbol: rustc_span::symbol::Symbol::intern(format!("{}", lit.value()).as_str()),
                suffix: None, // rustc_span::symbol::Symbol::intern(lit.suffix())
            }
        }
        _ => panic!("TODO: Implement pearlite literals"),
    }
}

fn translate_id(id: rustc_span::symbol::Ident) -> Ident {
    Ident::Unresolved(format!("{}", id))
}

fn translate_pearlite_type(sess: &Session, typ: syn::Type, span: Span) -> rustc_ast::ast::Ty {
    match typ {
        // syn::Type::Array(arr_ty) => {
        // BaseTyp::Array(match translate_pearlite(arr_ty.len, span) {

        //     _ => panic!()
        // }, Box::new(translate_pearlite_type(*arr_ty.elem, span))) }
        // syn::Type::BareFn(TypeBareFn) => ,
        // syn::Type::Group(TypeGroup) => ,
        // syn::Type::ImplTrait(TypeImplTrait) => ,
        // syn::Type::Infer(TypeInfer) => ,
        // syn::Type::Macro(TypeMacro) => ,
        // syn::Type::Never(TypeNever) => ,
        // syn::Type::Paren(TypeParen) => ,
        syn::Type::Path(syn::TypePath {
            qself: _,
            path:
                syn::Path {
                    leading_colon: _,
                    segments: s,
                },
        }) => {
            Ty {
                tokens: None,
                id: NodeId::MAX,
                kind: rustc_ast::TyKind::Path(
                    None,
                    rustc_ast::ast::Path {
                        span,
                        segments: s
                            .iter()
                            .map(|x| match x {
                                syn::PathSegment { ident: id, .. } => rustc_ast::ast::PathSegment {
                                    ident: translate_pearlite_ident(id.clone(), span),
                                    id: NodeId::MAX,
                                    args: None,
                                },
                            })
                            .collect(),
                        tokens: None,
                    },
                ),
                span, // tok.span.clone(),
            }
        }
        //     BaseTyp::Named(
        //     (
        //         TopLevelIdent(
        //             s.iter()
        //                 .fold("".to_string(), |s, x| match x {
        //                     syn::PathSegment { ident: id, .. } =>
        //                         (if s == "".to_string() { s } else { s + "::" }) + format!("{}", id.clone()).as_str(),
        //                 }),
        //         ),
        //         span,
        //     ),
        //     None,
        // )
        ,
        // syn::Type::Ptr(TypePtr) => ,
        // syn::Type::Reference(TypeReference) => ,
        // syn::Type::Slice(TypeSlice) => ,
        // syn::Type::TraitObject(TypeTraitObject) => ,
        // syn::Type::Tuple(TypeTuple) => ,
        // syn::Type::Verbatim(TokenStream) => ,
        _ => panic!("Type panic"),
    }
}

// translate_expr
pub(crate) fn translate_pearlite(
    sess: &Session,
    t: pearlite_syn::term::Term,
    span: Span,
) -> Quantified<(Ident, Ty), Expr> {
    let kind = match t {
        // pearlite_syn::term::Term::Array(_) => RcDoc::as_string("TODOArray"),
        pearlite_syn::term::Term::Binary(pearlite_syn::term::TermBinary { left, op, right }) => {
            if translate_pearlite_binop(op) == ast::BinOpKind::Eq {
                return Quantified::Eq(
                    Box::new(translate_pearlite(sess, *left, span)),
                    Box::new(translate_pearlite(sess, *right, span)),
                )
            }
            
            ExprKind::Binary(
                rustc_span::source_map::Spanned {
                    node: translate_pearlite_binop(op),
                    span,
                },
                P(translate_pearlite_unquantified(sess, *left, span).unwrap()),
                P(translate_pearlite_unquantified(sess, *right, span).unwrap()),
            )
        }
        // pearlite_syn::term::Term::Block(pearlite_syn::term::TermBlock { block, .. }) => {
        //     ExprKind::Block(
        //         P(rustc_ast::ast::Block {
        //             stmts: block
        //                 .stmts
        //                 .map(|x| Stmt {
        //                     id: NodeId::from_usize(0),
        //                     kind: match x {
        //                         pearlite_syn::term::TermStmt::Local(pearlite_syn::term::TLocal { let_token, pat, init, semi_token }) =>
        //                             rustc_ast::ast::StmtKind::Local(P(rustc_ast::ast::Local {id: NodeId::from_usize(0), pat: P(pat), None, })),
        //                     },
        //                     span,
        //                 })
        //                 .collect(),
        //             id: NodeId::from_usize(0),
        //             rules: BlockCheckMode::Default,
        //             span,
        //             tokens: None,
        //             could_be_bare_literal: true,
        //         }),
        //         None,
        //     )
        // }
        pearlite_syn::term::Term::Call(pearlite_syn::term::TermCall { func, args, .. }) => {
            ExprKind::Call(
                P(translate_pearlite_unquantified(sess, *func, span).unwrap()),
                args.into_iter()
                    .map(|x| P(translate_pearlite_unquantified(sess, x, span).unwrap()))
                    .collect(),
            )
        }
        //         pearlite_syn::term::Term::Cast(_) => RcDoc::as_string("TODOCast"),
        //         pearlite_syn::term::Term::Field(pearlite_syn::term::TermField { base, member, .. }) => {
        //             RcDoc::as_string("TODOField")
        //         }
        //         pearlite_syn::term::Term::Group(_) => RcDoc::as_string("TODOGroup"),
        //         pearlite_syn::term::Term::If(pearlite_syn::term::TermIf {
        //             cond,
        //             then_branch,
        //             else_branch,
        //             ..
        //         }) => RcDoc::as_string("TODOIf"),
        pearlite_syn::term::Term::Index(pearlite_syn::term::TermIndex { expr, index, .. }) => {
            ExprKind::Index(
                P(translate_pearlite_unquantified(sess, *expr, span).unwrap()),
                P(translate_pearlite_unquantified(sess, *index, span).unwrap()),
            )
        }
        //         pearlite_syn::term::Term::Let(_) => RcDoc::as_string("TODOLet"),
        pearlite_syn::term::Term::Lit(pearlite_syn::term::TermLit { ref lit }) => {
            ExprKind::Lit(translate_pearlite_lit(lit.clone(), span))
        }
        //         pearlite_syn::term::Term::Match(pearlite_syn::term::TermMatch { expr, arms, .. }) => {
        //             RcDoc::as_string("TODOMatch")
        //         }
        pearlite_syn::term::Term::MethodCall(pearlite_syn::term::TermMethodCall {
            receiver,
            method,
            turbofish, // TODO: turbofish??
            args,
            ..
        }) => {
            let mut arg_expr = args.into_iter()
                    .map(|x| P(translate_pearlite_unquantified(sess, x, span).unwrap())).collect();
            let mut receiver_expr = P(
                translate_pearlite_unquantified(sess, *receiver, span).unwrap()
            );
            ExprKind::MethodCall(
                Box::new(
                    ast::MethodCall {
                        seg: PathSegment {
                            ident: translate_pearlite_ident(method, span),
                            id: NodeId::MAX,
                            args: None,
                        },
                        receiver: receiver_expr,
                        args: arg_expr,
                        span,
                    }
                ),
            )
        }
        pearlite_syn::term::Term::Paren(pearlite_syn::term::TermParen { expr, .. }) => {
            // match expr.clone() {
            // ExprKind::Paren(P(
            return translate_pearlite(sess, *expr, span); // _unquantified.unwrap()
                                                          // ))
                                                          // }
        }
        pearlite_syn::term::Term::Path(pearlite_syn::term::TermPath {
            inner:
                syn::ExprPath {
                    attrs: _,
                    qself: _,
                    path:
                        syn::Path {
                            leading_colon: _,
                            segments: s,
                        },
                },
        }) => ExprKind::Path(
            None,
            Path {
                span,
                segments: s
                    .iter()
                    .map(|x| match x {
                        syn::PathSegment {
                            ident: id,
                            arguments: args,
                            ..
                        } => rustc_ast::ast::PathSegment {
                            ident: translate_pearlite_ident(id.clone(), span),
                            id: NodeId::MAX,
                            args: match args {
                                syn::PathArguments::None => None,
                                syn::PathArguments::AngleBracketed(
                                    syn::AngleBracketedGenericArguments { args: ab_args, .. },
                                ) => Some(P(rustc_ast::ast::AngleBracketed(
                                    rustc_ast::ast::AngleBracketedArgs {
                                        span,
                                        args: ab_args
                                            .into_iter()
                                            .map(|arg| match arg {
                                                syn::GenericArgument::Type(ty) => {
                                                    rustc_ast::ast::AngleBracketedArg::Arg(
                                                        rustc_ast::ast::GenericArg::Type(P(
                                                            translate_pearlite_type(
                                                                sess,
                                                                ty.clone(),
                                                                span,
                                                            ),
                                                        )),
                                                    )
                                                }
                                                _ => panic!("Missing cases"),
                                            })
                                            .collect(),
                                    },
                                ))),
                                syn::PathArguments::Parenthesized(pga) => None,
                            },
                        },
                    })
                    .collect(),
                tokens: None,
            },
        ),
        //         pearlite_syn::term::Term::Range(_) => RcDoc::as_string("TODORange"),
        //         pearlite_syn::term::Term::Repeat(_) => RcDoc::as_string("TODORepeat"),
        //         pearlite_syn::term::Term::Struct(_) => RcDoc::as_string("TODOStruct"),
        //         pearlite_syn::term::Term::Tuple(pearlite_syn::term::TermTuple { elems, .. }) => {
        //             make_paren(RcDoc::intersperse(
        //                 elems
        //                     .into_iter()
        //                     .map(|x| make_paren(translate_pearlite(x, top_ctx, idents.clone()))),
        //                 RcDoc::as_string(",").append(RcDoc::space()),
        //             ))
        //         }
        //         pearlite_syn::term::Term::Type(ty) => RcDoc::as_string("TODOType"),
        pearlite_syn::term::Term::Unary(pearlite_syn::term::TermUnary { op, expr }) => {
            if let syn::UnOp::Not(_) = op {
                return Quantified::Not(
                    Box::new(translate_pearlite(sess, *expr, span)),
                )
            }
            else {
                panic!("translate_pearlite_todo unary: {:#?} {:#?}\n", op, expr);
            }
        //             RcDoc::as_string("TODOUnary").append(translate_pearlite(*expr, top_ctx, idents.clone()))
        }
        //         pearlite_syn::term::Term::Final(pearlite_syn::term::TermFinal { term, .. }) => {
        //             RcDoc::as_string("TODOFinal").append(translate_pearlite(*term, top_ctx, idents.clone()))
        //         }
        pearlite_syn::term::Term::Model(pearlite_syn::term::TermModel { term, .. }) => {
            // TODO: Does not make sence in combination with hacspec!
            return translate_pearlite(sess, *term, span); // Model supported? (@)
        }
        //         pearlite_syn::term::Term::Verbatim(_) => RcDoc::as_string("TODOVerbatim"),
        pearlite_syn::term::Term::LogEq(pearlite_syn::term::TermLogEq { lhs, rhs, .. }) => {
            return Quantified::Eq(
                Box::new(translate_pearlite(sess, *lhs, span)),
                Box::new(translate_pearlite(sess, *rhs, span)),
            )
        }
        pearlite_syn::term::Term::Impl(pearlite_syn::term::TermImpl { hyp, cons, .. }) => {
            return Quantified::Implication(
                Box::new(translate_pearlite(sess, *hyp, span)),
                Box::new(translate_pearlite(sess, *cons, span)),
            );

            // make_paren(translate_pearlite(*hyp, top_ctx, idents.clone()))
            //     .append(RcDoc::space())
            //     .append(RcDoc::as_string("->"))
            //     .append(RcDoc::space())
            //     .append(make_paren(translate_pearlite(*cons, top_ctx, idents.clone())))
        }
        pearlite_syn::term::Term::Forall(pearlite_syn::term::TermForall { args, term, .. }) => {
            return Quantified::Forall(
                args.iter()
                    .map(|x| {
                        (
                            translate_id(translate_pearlite_ident(x.ident.clone(), span)),
                            translate_pearlite_type(sess, *x.ty.clone(), span),
                        )
                    })
                    .collect(),
                Box::new(translate_pearlite(sess, *term, span)),
            );
        }
        //         pearlite_syn::term::Term::Exists(pearlite_syn::term::TermExists { args, term, .. }) => {
        //             RcDoc::as_string("exists")
        //                 .append(RcDoc::space())
        //                 .append(
        //                     args.iter()
        //                         .fold(RcDoc::nil(), |rs, x| rs.append(x.ident.to_string())),
        //                 )
        //                 .append(RcDoc::as_string(","))
        //                 .append(RcDoc::space())
        //                 .append(translate_pearlite(*term, top_ctx, idents.clone()))
        //         }
        //         pearlite_syn::term::Term::Absurd(_) => RcDoc::as_string("TODOAbsurd"),
        //         pearlite_syn::term::Term::Pearlite(term) => RcDoc::as_string("TODOPearlite"),
        //         pearlite_syn::term::Term::__Nonexhaustive => RcDoc::as_string("TODONonexhaustive"),
        //     }
        a => {
            panic!("translate_pearlite_todo: {:#?}\n", a);
            // ExprKind::Underscore
        }
    };

    Quantified::Unquantified(Expr {
        id: NodeId::from_usize(0),
        kind,
        span,
        attrs: AttrVec::new(),
        tokens: None,
    })
}

pub(crate) fn translate_quantified_expr(
    sess: &Session,
    specials: &SpecialNames,
    qe: Quantified<(Ident, Ty), Expr>,
) -> Quantified<(Ident, Spanned<BaseTyp>), Spanned<Expression>> {
    match qe {
        Quantified::Unquantified(expr) => {
            Quantified::Unquantified(translate_expr_expects_exp(sess, specials, &expr).unwrap())
        }
        Quantified::Forall(ids, term) => Quantified::Forall(
            ids.into_iter()
                .map(|(id, ty)| {
                    (
                        id,
                        crate::ast_to_rustspec::translate_base_typ(sess, &ty).unwrap(),
                    )
                })
                .collect(),
            Box::new(translate_quantified_expr(sess, specials, *term)),
        ),
        Quantified::Exists(ids, term) => Quantified::Exists(
            ids.into_iter()
                .map(|(id, ty)| {
                    (
                        id,
                        crate::ast_to_rustspec::translate_base_typ(sess, &ty).unwrap(),
                    )
                })
                .collect(),
            Box::new(translate_quantified_expr(sess, specials, *term)),
        ),
        Quantified::Implication(a, b) => Quantified::Implication(
            Box::new(translate_quantified_expr(sess, specials, *a)),
            Box::new(translate_quantified_expr(sess, specials, *b)),
        ),
        Quantified::Eq(a, b) => Quantified::Eq(
            Box::new(translate_quantified_expr(sess, specials, *a)),
            Box::new(translate_quantified_expr(sess, specials, *b)),
        ),
        Quantified::Not(a) => {
            Quantified::Not(Box::new(translate_quantified_expr(sess, specials, *a)))
        }
    }
}

fn binop_text(op: rustc_ast::token::BinOpToken) -> String {
    match op {
        rustc_ast::token::BinOpToken::Plus => "+".to_string(),
        rustc_ast::token::BinOpToken::Minus => "-".to_string(),
        rustc_ast::token::BinOpToken::Star => "*".to_string(),
        rustc_ast::token::BinOpToken::Slash => "/".to_string(),
        rustc_ast::token::BinOpToken::Percent => "%".to_string(),
        rustc_ast::token::BinOpToken::Caret => "^".to_string(),
        rustc_ast::token::BinOpToken::And => "&".to_string(),
        rustc_ast::token::BinOpToken::Or => "|".to_string(),
        rustc_ast::token::BinOpToken::Shl => "<<".to_string(),
        rustc_ast::token::BinOpToken::Shr => ">>".to_string(),
    }
}

fn tokentree_text(x: TokenTree) -> String {
    match x {
        TokenTree::Token(tok, ..) => match tok.kind {
            TokenKind::Eq => "=".to_string(),
            TokenKind::Lt => "<".to_string(),
            TokenKind::Le => "<=".to_string(),
            TokenKind::EqEq => "==".to_string(),
            TokenKind::Ne => "!=".to_string(),
            TokenKind::Ge => ">=".to_string(),
            TokenKind::Gt => ">".to_string(),
            TokenKind::AndAnd => "&&".to_string(),
            TokenKind::OrOr => "||".to_string(),
            TokenKind::Not => "!".to_string(),
            TokenKind::Tilde => "`".to_string(),
            TokenKind::BinOp(op) => binop_text(op),
            TokenKind::BinOpEq(op) => binop_text(op) + "=",
            TokenKind::At => "@".to_string(),
            TokenKind::Dot => ".".to_string(),
            TokenKind::DotDot => "..".to_string(),
            TokenKind::DotDotDot => "...".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::Semi => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::ModSep => "::".to_string(),
            TokenKind::RArrow => "->".to_string(),
            TokenKind::LArrow => "<-".to_string(),
            TokenKind::FatArrow => "=>".to_string(),
            TokenKind::Pound => "€".to_string(),
            TokenKind::Dollar => "$".to_string(),
            TokenKind::Question => "$".to_string(),
            TokenKind::Literal(x) => format![" {} ", x].to_string(),
            TokenKind::Ident(sym, _) => format![" {} ", sym].to_string(),
            y => {
                panic!(" (TODO: {:?})", y);
            }
        },
        TokenTree::Delimited(_, delim_token, inner) => {
            let (left, right) = match delim_token {
                Delimiter::Parenthesis => ("(", ")"),
                Delimiter::Bracket => ("[", "]"),
                Delimiter::Brace => ("{", "}"),
                Delimiter::Invisible => ("", ""),
            };

            left.to_string()
                + &inner
                    .trees()
                    .fold("".to_string(), |s, x| s + &tokentree_text(x.clone()))
                + right
        }
    }
}

pub(crate) fn attribute_requires(attr: &Attribute) -> Option<String> {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "requires" => {
            let inner = crate::ast_to_rustspec::get_delimited_tree(attr.clone())?;
            let textify = inner
                .trees()
                .fold("".to_string(), |s, x| s + &tokentree_text(x.clone()));
            Some(textify)
        }
        _ => None,
    }
}

pub(crate) fn attribute_ensures(attr: &Attribute) -> Option<String> {
    let attr_name = attr.name_or_empty().to_ident_string();
    match attr_name.as_str() {
        "ensures" => {
            let inner = crate::ast_to_rustspec::get_delimited_tree(attr.clone())?;
            let textify = inner
                .trees()
                .fold("".to_string(), |s, x| s + &tokentree_text(x.clone()));
            Some(textify)
        }
        _ => None,
    }
}


fn resolve_quantified_identifiers(
    ids: Vec<(Ident, Spanned<BaseTyp>)>,
    name_context: &crate::name_resolution::NameContext,
) -> (Vec<(Ident, Spanned<BaseTyp>)>, crate::name_resolution::NameContext) {
    let new_ids: Vec<(Ident, Spanned<BaseTyp>)> = ids
        .iter()
        .map(|(x, ty)| {
            let new_x = match x {
                Ident::Unresolved(s) => crate::name_resolution::to_fresh_ident(s, false),
                _ => panic!("should not happen"),
            };

            (new_x, ty.clone())
        })
        .collect();

    let new_context = ids
        .iter()
        .zip(new_ids.clone().iter())
        .fold(name_context.clone(), |ctx, ((x, _), (new_x, _))| {
            crate::name_resolution::add_name(x, &new_x.clone(), ctx)
        });

    (new_ids, new_context)
}

pub(crate) fn resolve_quantified_expression(
    sess: &Session,
    qe: Quantified<(Ident, Spanned<BaseTyp>), Spanned<Expression>>,
    name_context: &crate::name_resolution::NameContext,
    top_level_ctx: &TopLevelContext,
) -> crate::name_resolution::ResolutionResult<Quantified<(Ident, Spanned<BaseTyp>), Spanned<Expression>>> {
    match qe {
        Quantified::Unquantified(e) => Ok(Quantified::Unquantified(crate::name_resolution::resolve_expression(
            sess,
            e,
            name_context,
            top_level_ctx,
        )?)),
        Quantified::Forall(ids, qe2) => {
            let (new_ids, new_context) = resolve_quantified_identifiers(ids, name_context);
            let qe2_resolved =
                resolve_quantified_expression(sess, *qe2, &new_context, top_level_ctx)?;

            Ok(Quantified::Forall(new_ids, Box::new(qe2_resolved)))
        }
        Quantified::Exists(ids, qe2) => {
            let (new_ids, new_context) = resolve_quantified_identifiers(ids, name_context);
            Ok(Quantified::Exists(
                new_ids,
                Box::new(resolve_quantified_expression(
                    sess,
                    *qe2,
                    &new_context,
                    top_level_ctx,
                )?),
            ))
        }
        Quantified::Implication(a, b) => Ok(Quantified::Implication(
            Box::new(resolve_quantified_expression(
                sess,
                *a,
                name_context,
                top_level_ctx,
            )?),
            Box::new(resolve_quantified_expression(
                sess,
                *b,
                name_context,
                top_level_ctx,
            )?),
        )),
        Quantified::Eq(a, b) => Ok(Quantified::Eq(
            Box::new(resolve_quantified_expression(
                sess,
                *a,
                name_context,
                top_level_ctx,
            )?),
            Box::new(resolve_quantified_expression(
                sess,
                *b,
                name_context,
                top_level_ctx,
            )?),
        )),
        Quantified::Not(x) => Ok(Quantified::Not(Box::new(resolve_quantified_expression(
            sess,
            *x,
            name_context,
            top_level_ctx,
        )?))),
    }
}

pub(crate) fn translate_quantified_expression<'a>(
    qe: Quantified<(Ident, Spanned<BaseTyp>), Spanned<Expression>>,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    match qe {
        Quantified::Unquantified((e, _)) => crate::rustspec_to_coq::translate_expression(e, top_ctx),
        Quantified::Forall(ids, qe2) => RcDoc::as_string("forall")
            .append(RcDoc::space())
            .append(RcDoc::intersperse(
                ids.into_iter().map(|(x, (typ, _))| {
                    crate::rustspec_to_coq_base::translate_ident(x.clone())
                        .append(RcDoc::as_string(" : "))
                        .append(crate::rustspec_to_coq::translate_base_typ(typ))
                }),
                RcDoc::space(),
            ))
            .append(RcDoc::as_string(","))
            .append(RcDoc::line())
            .append(translate_quantified_expression(*qe2, top_ctx)),
        Quantified::Exists(ids, qe2) => RcDoc::as_string("exists")
            .append(RcDoc::space())
            .append(RcDoc::intersperse(
                ids.into_iter().map(|(x, (typ, _))| {
                    crate::rustspec_to_coq_base::translate_ident(x.clone())
                        .append(RcDoc::as_string(" : "))
                        .append(crate::rustspec_to_coq::translate_base_typ(typ))
                }),
                RcDoc::space(),
            ))
            .append(RcDoc::as_string(","))
            .append(RcDoc::line())
            .append(translate_quantified_expression(*qe2, top_ctx)),
        Quantified::Implication(qe2, qe3) => translate_quantified_expression(*qe2, top_ctx)
            .append(RcDoc::space())
            .append(RcDoc::as_string("->"))
            .append(RcDoc::line())
            .append(translate_quantified_expression(*qe3, top_ctx)),
        Quantified::Eq(qe2, qe3) => translate_quantified_expression(*qe2, top_ctx)
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .append(RcDoc::space())
            .append(translate_quantified_expression(*qe3, top_ctx)),
        Quantified::Not(qex) => RcDoc::as_string("~")
            .append(RcDoc::space())
            .append(crate::rustspec_to_coq_base::make_paren(translate_quantified_expression(*qex, top_ctx))),
    }
}
