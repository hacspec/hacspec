use rustc_ast;
use rustc_ast::ast::{
    self, AngleBracketedArg, Async, BindingMode, Const, Crate, Defaultness, Extern, FnRetTy,
    GenericArg, GenericArgs, ItemKind, Mutability, PatKind, Ty, TyKind, Unsafe,
};
use rustc_session::Session;
use rustc_span::symbol::Ident;

use crate::rustspec::*;

type TranslationResult<T> = Result<T, ()>;

fn check_vec<T>(v: Vec<TranslationResult<T>>) -> TranslationResult<Vec<T>> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

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
            Some(generic_args) => match generic_args.clone().into_inner() {
                GenericArgs::Parenthesized(_) => {
                    sess.span_err(
                        path.span,
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
                                Ok(Some(Box::new(typ_arg?)))
                            }
                            Some(AngleBracketedArg::Arg(GenericArg::Lifetime(_))) => {
                                sess.span_err(args.span, "lifetime type parameters are not allowed in Rustspect");
                                Err(())
                            }
                            Some(AngleBracketedArg::Arg(GenericArg::Const(_))) => {
                                sess.span_err(args.span, "const generics are not allowed in Rustspec");
                                Err(())
                            }
                        }
                    }
                }
            },
        },
    };
    Ok(Path {location, arg: arg?})
}

fn translate_base_typ(sess: &Session, ty: &Ty) -> TranslationResult<Spanned<BaseTyp>> {
    match &ty.kind {
        TyKind::Path(None, path) => Ok((BaseTyp::Named(translate_path(sess, path)?), ty.span)),
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

fn translate_block(sess: &Session, b: &ast::Block) -> TranslationResult<Spanned<Block>> {
    Ok((Vec::new(), b.span))
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
