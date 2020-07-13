use rustc_ast::ast::{
    self, Async, BindingMode, Const, Crate, Defaultness, Extern, FnRetTy, ItemKind,
    Mutability, PatKind, Ty, Unsafe,
};
use rustc_session::Session;
use rustc_span::symbol::Ident;

use crate::rustspec::*;

fn check_vec<T>(v: Vec<Result<T, ()>>) -> Result<Vec<T>, ()> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn translate_base_typ(sess: &Session, ty: &Ty) -> Result<Spanned<BaseTyp>, ()> {
    panic!()
}

fn translate_typ(sess: &Session, ty: &Ty) -> Result<Spanned<Typ>, ()> {
    panic!()
}

fn translate_block(sess: &Session, b: &ast::Block) -> Result<Spanned<Block>, ()> {
    panic!()
}

fn translate_items(sess: &Session, i: &ast::Item) -> Result<Item, ()> {
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
            let fn_inputs: Vec<Result<(Spanned<Ident>, Spanned<Typ>), ()>> = sig
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

pub fn translate(sess: &Session, krate: &Crate) -> Result<Program, ()> {
    let items = &krate.module.items;
    check_vec(items.into_iter().map(|i| Ok((translate_items(sess, &i)?, i.span))).collect())
}
