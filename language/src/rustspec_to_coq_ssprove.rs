use crate::name_resolution::TopLevelContext;
use crate::rustspec::*;
use core::iter::IntoIterator;
use pretty::RcDoc;
use rustc_session::Session;
use std::fs::File;
use std::io::Write;
use std::path;

use crate::rustspec_to_coq_base::*;
use crate::rustspec_to_coq_ssprove_pure;
use crate::rustspec_to_coq_ssprove_state;

fn translate_enum_name<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    translate_toplevel_ident(enum_name)
}

fn translate_base_typ<'a>(tau: BaseTyp) -> RcDoc<'a, ()> {
    match tau {
        BaseTyp::Unit => RcDoc::as_string("unit_ChoiceEquality"),
        BaseTyp::Bool => RcDoc::as_string("bool_ChoiceEquality"),
        BaseTyp::UInt8 => RcDoc::as_string("int8"),
        BaseTyp::Int8 => RcDoc::as_string("int8"),
        BaseTyp::UInt16 => RcDoc::as_string("int16"),
        BaseTyp::Int16 => RcDoc::as_string("int16"),
        BaseTyp::UInt32 => RcDoc::as_string("int32"),
        BaseTyp::Int32 => RcDoc::as_string("int32"),
        BaseTyp::UInt64 => RcDoc::as_string("int64"),
        BaseTyp::Int64 => RcDoc::as_string("int64"),
        BaseTyp::UInt128 => RcDoc::as_string("int128"),
        BaseTyp::Int128 => RcDoc::as_string("int128"),
        BaseTyp::Usize => RcDoc::as_string("uint_size"),
        BaseTyp::Isize => RcDoc::as_string("int_size"),
        BaseTyp::Str => RcDoc::as_string("string"),
        BaseTyp::Seq(tau) => {
            let tau: BaseTyp = tau.0;
            RcDoc::as_string("seq")
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .group()
        }
        // todo?
        BaseTyp::Enum(_cases, _type_args) => {
            unimplemented!()
        }
        BaseTyp::Array(size, tau) => {
            let tau = tau.0;
            RcDoc::as_string("nseq")
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .append(RcDoc::space())
                .append(RcDoc::as_string(match &size.0 {
                    ArraySize::Ident(id) => format!("{}", id),
                    ArraySize::Integer(i) => format!("{}", i),
                }))
                .group()
        }
        BaseTyp::Named((ident, _span), args) => match args {
            None => translate_ident(Ident::TopLevel(ident)),
            Some(args) => make_paren(
                translate_ident(Ident::TopLevel(ident))
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(
                        args.iter().map(|arg| translate_base_typ(arg.0.clone())),
                        RcDoc::space(),
                    )),
            ),
        },
        BaseTyp::Variable(id) => RcDoc::as_string(format!("t{}", id.0)),
        BaseTyp::Tuple(args) => {
            if args.len() == 0 {
                RcDoc::as_string("unit_ChoiceEquality")
            } else {
                make_typ_tuple(args.into_iter().map(|(arg, _)| translate_base_typ(arg)))
            }
        }
        BaseTyp::NaturalInteger(_secrecy, modulo, _bits) => RcDoc::as_string("nat_mod")
            .append(RcDoc::space())
            .append(RcDoc::as_string(format!("0x{}", &modulo.0)))
            .append(RcDoc::hardline()),
    }
}

fn translate_typ<'a>((_, (tau, _)): Typ) -> RcDoc<'a, ()> {
    translate_base_typ(tau)
}

fn translate_item<'a>(item: DecoratedItem, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match item.item.clone() {
        Item::FnDecl((f, f_span), sig, (b, b_span)) => {
            let (block_vars, _block_var_loc_defs) =
                rustspec_to_coq_ssprove_state::fset_and_locations(sig.mutable_vars.clone());

            rustspec_to_coq_ssprove_pure::translate_item(
                    DecoratedItem {
                        item: Item::FnDecl(
                            (
                                TopLevelIdent {
                                    string: f.string.clone() + "_pure",
                                    ..f.clone()
                                },
                                f_span.clone(),
                            ),
                            sig.clone(),
                            (b.clone(), b_span.clone()),
                        ),
                        ..item.clone()
                    },
                    top_ctx,
                )
                .append(RcDoc::line())
                .append(RcDoc::line())
                .append(rustspec_to_coq_ssprove_state::translate_item(
                    DecoratedItem {
                        item: Item::FnDecl(
                            (
                                TopLevelIdent {
                                    string: f.string.clone() + "_state",
                                    ..f.clone()
                                },
                                f_span.clone(),
                            ),
                            sig.clone(),
                            (b.clone(), b_span.clone()),
                        )
                        .clone(),
                        ..item.clone()
                    },
                    top_ctx,
                ))
                // .append(block_var_loc_defs)
                // .append(RcDoc::line())
                // .append(RcDoc::as_string("Program "))
                // .append(
                //     make_let_binding(
                //         translate_ident(Ident::TopLevel(f.clone())).append(RcDoc::as_string("_state"))
                //             .append(RcDoc::line())
                //             .append(if sig.args.len() > 0 {
                //                 RcDoc::intersperse(
                //                     sig.args.iter().map(|((x, _), (tau, _))| {
                //                         make_paren(
                //                             translate_ident(x.clone())
                //                                 .append(RcDoc::space())
                //                                 .append(RcDoc::as_string(":"))
                //                                 .append(RcDoc::space())
                //                                 .append(translate_typ(tau.clone())),
                //                         )
                //                     }),
                //                     RcDoc::line(),
                //                 )
                //             } else {
                //                 RcDoc::nil()
                //             })
                //             .append(RcDoc::line())
                //             .append(RcDoc::as_string(": code"))
                //             .append(RcDoc::space())
                //             .append(make_paren(block_vars.clone()))
                //             .append(RcDoc::space())
                //             .append(RcDoc::as_string("[interface]"))
                //             .append(RcDoc::space())
                //             .append(make_paren(
                //                 RcDoc::as_string("@ct")
                //                     .append(RcDoc::space())
                //                     .append(make_paren(translate_base_typ(sig.ret.0.clone())))
                //             ))
                //             .group(),
                //         None,
                //         false,
                //     block_exprs.group(),
                //     true,
                //     false,
                //     )
                // ).append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))
                .append(RcDoc::line())
                .append(RcDoc::line())
                .append(RcDoc::as_string("Program"))
                .append(RcDoc::space())
                .append(rustspec_to_coq_ssprove_pure::make_let_binding(
                    translate_ident(Ident::TopLevel(f.clone()))
                        .append(RcDoc::line())
                        .append(if sig.args.len() > 0 {
                            RcDoc::intersperse(
                                sig.args.iter().map(|((x, _), (tau, _))| {
                                    make_paren(
                                        translate_ident(x.clone())
                                            .append(RcDoc::space())
                                            .append(RcDoc::as_string(":"))
                                            .append(RcDoc::space())
                                            .append(translate_typ(tau.clone())),
                                    )
                                }),
                                RcDoc::line(),
                            )
                        } else {
                            RcDoc::nil()
                        })
                        .append(RcDoc::line())
                        .append(
                            RcDoc::as_string(":")
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("both"))
                                .append(RcDoc::space())
                                .append(make_paren(block_vars.clone()))
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("[interface]"))
                                .append(RcDoc::space())
                                .append(translate_base_typ(sig.ret.0.clone()))
                                .group(),
                        ),
                    None,
                    RcDoc::as_string("{|")
                        .append(RcDoc::line())
                        .append(RcDoc::as_string("is_pure := "))
                        .append(
                            translate_ident(Ident::TopLevel(f.clone()))
                                .append(RcDoc::as_string("_pure")),
                        )
                        .append(RcDoc::space())
                        .append(if sig.args.len() > 0 {
                            RcDoc::intersperse(
                                sig.args.iter().map(|((x, _), (tau, _))| {
                                    make_paren(
                                        translate_ident(x.clone())
                                            .append(RcDoc::space())
                                            .append(RcDoc::as_string(":"))
                                            .append(RcDoc::space())
                                            .append(translate_typ(tau.clone())),
                                    )
                                }),
                                RcDoc::line(),
                            )
                        } else {
                            RcDoc::nil()
                        })
                        .append(RcDoc::as_string(";"))
                        .append(RcDoc::line())
                        .append(RcDoc::as_string("is_state := "))
                        .append(
                            translate_ident(Ident::TopLevel(f.clone()))
                                .append(RcDoc::as_string("_state")),
                        )
                        .append(RcDoc::space())
                        .append(if sig.args.len() > 0 {
                            RcDoc::intersperse(
                                sig.args.iter().map(|((x, _), (tau, _))| {
                                    make_paren(
                                        translate_ident(x.clone())
                                            .append(RcDoc::space())
                                            .append(RcDoc::as_string(":"))
                                            .append(RcDoc::space())
                                            .append(translate_typ(tau.clone())),
                                    )
                                }),
                                RcDoc::line(),
                            )
                        } else {
                            RcDoc::nil()
                        })
                        .append(RcDoc::as_string(";"))
                        .append(RcDoc::line())
                        .append(RcDoc::as_string("|}")),
                    true,
                ))
                .append(RcDoc::line())
                .append(RcDoc::as_string(format!(
                    "Next Obligation.\n\
                       intros.\n\
                       unfold {name}_pure.\n\
                       unfold {name}_state.\n\
                       \n\
                       unfold prog.\n\
                       Admitted.", name=f.string)))
        }
        _ => rustspec_to_coq_ssprove_pure::translate_item(item, top_ctx),
    }
}

fn translate_program<'a>(p: &'a Program, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    RcDoc::concat(p.items.iter().map(|(i, _)| {
        translate_item(i.clone(), top_ctx)
            .append(RcDoc::hardline())
            .append(RcDoc::hardline())
    }))
}

pub fn translate_and_write_to_file(
    sess: &Session,
    p: &Program,
    file: &str,
    top_ctx: &TopLevelContext,
) {
    let file = file.trim();
    let path = path::Path::new(file);
    let mut file = match File::create(&path) {
        Err(why) => {
            sess.err(format!("Unable to write to output file {}: \"{}\"", file, why).as_str());
            return;
        }
        Ok(file) => file,
    };
    let width = 80;
    let mut w = Vec::new();
    // let module_name = path.file_stem().unwrap().to_str().unwrap();
    write!(
        file,
        "(** This file was automatically generated using Hacspec **)\n\
         From Crypt Require Import choice_type Package Prelude.\n\
         Import PackageNotation.\n\
         From extructures Require Import ord fset.\n\
         From CoqWord Require Import ssrZ word.\n\
         From Jasmin Require Import word.\n\
         \n\
         From Coq Require Import ZArith.\n\
         Import List.ListNotations.\n\
         Open Scope list_scope.\n\
         Open Scope Z_scope.\n\
         Open Scope bool_scope.\n\n\
         \n\
         Require Import ChoiceEquality.\n\
         Require Import LocationUtility.\n\
         Require Import Hacspec_Lib_Comparable.\n\
         Require Import Hacspec_Lib_Pre.\n\
         Require Import Hacspec_Lib.\n\
         \n\
         Open Scope hacspec_scope.\n\n\
         Obligation Tactic :=\n\
         (intros ; do 2 ssprove_valid'_2) ||\n\
         (try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)\n\
         \n",
    )
    .unwrap();
    translate_program(p, top_ctx).render(width, &mut w).unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
