use crate::name_resolution::{DictEntry, TopLevelContext};
use crate::rustspec::*;
use core::iter::IntoIterator;
use core::slice::Iter;
use heck::TitleCase;
use itertools::Itertools;
use pretty::RcDoc;
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use std::fs::File;
use std::io::Write;
use std::path;

use crate::rustspec_to_coq_base::*;

fn make_get_binding<'a>(pat: Pattern, typ: Option<RcDoc<'a, ()>>) -> RcDoc<'a, ()> {
    match typ {
        Some(typ) => RcDoc::as_string("'").append(make_paren(
            translate_pattern(pat.clone()).append(" : ").append(typ),
        )),
        None => translate_pattern(pat.clone()),
    }
    .append(RcDoc::space())
    .append(RcDoc::as_string("←"))
    .append(RcDoc::space())
    .append(RcDoc::as_string("get"))
    .append(RcDoc::space())
    .append(
        translate_pattern(pat.clone())
            .append(RcDoc::as_string("_loc"))
            .group(),
    )
    .append(RcDoc::space())
    .append(RcDoc::as_string(";;"))
    .append(RcDoc::line())
}

fn make_put_binding<'a>(
    pat: Pattern,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    make_let_binding(pat.clone(), typ, expr.group(), true)
        .append(RcDoc::as_string("#put"))
        .append(RcDoc::space())
        .append(
            translate_pattern(pat.clone())
                .append(RcDoc::as_string("_loc"))
                .group(),
        )
        .append(RcDoc::space())
        .append(RcDoc::as_string(":= "))
        .group()
        .append(translate_pattern(pat.clone()))
        .nest(2)
        .append(RcDoc::space())
        .append(RcDoc::as_string(";;"))
        .append(RcDoc::hardline())
}

// match pat.clone() {
//     Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
//     _ => RcDoc::nil(),
// }
// .append(translate_pattern_tick(pat.clone()))
fn make_let_binding<'a>(
    pat: Pattern,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
    do_bind: bool,
) -> RcDoc<'a, ()> {
    RcDoc::as_string(if do_bind { "" } else { "let" })
        .append(RcDoc::space())
        .append(
            match pat.clone() {
                // If the pattern is a tuple, expand it
                Pattern::Tuple(_) => RcDoc::as_string("'").append(translate_pattern(pat.clone())),
                _ => match typ.clone() {
                    None => translate_pattern_tick(pat.clone()),
                    Some(tau) => RcDoc::as_string("'").append(make_paren(
                        translate_pattern(pat.clone())
                            .append(RcDoc::space())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(tau),
                    )),
                },
            }
            .group(),
        )
        .append(RcDoc::space())
        .append(if do_bind {
            RcDoc::as_string("←")
        } else {
            RcDoc::as_string(":=")
        })
        .group()
        .append(RcDoc::line().append(make_paren(expr.group())))
        .nest(2)
        .append(if let Pattern::Tuple(_) = pat.clone() {
            if !do_bind {
                // TODO: typ after + do_bind
                match typ.clone() {
                    None => RcDoc::nil(),
                    Some(tau) => RcDoc::space()
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(tau),
                }
            } else {
                RcDoc::nil()
            }
        } else {
            RcDoc::nil()
        })
        .append(
            RcDoc::space()
                .append(if do_bind {
                    RcDoc::as_string(";;")
                } else {
                    RcDoc::as_string("in")
                })
                .append(RcDoc::hardline()),
        )
}

fn make_definition<'a>(
    name: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    RcDoc::as_string("Definition")
        .append(RcDoc::space())
        .append(name.clone())
        .append(RcDoc::space())
        .append(
            match typ.clone() {
                None => RcDoc::nil(),
                Some(tau) => RcDoc::as_string(":").append(RcDoc::space()).append(tau),
            }
            .group(),
        )
        .append(RcDoc::space())
        .append(RcDoc::as_string(":="))
        .group()
        .append(RcDoc::line().append(make_paren(expr.group())))
        .nest(2)
        .append(RcDoc::as_string("."))
}

fn code_block_wrap<'a>(
    expr: RcDoc<'a, ()>,
    location_vars: Option<RcDoc<'a, ()>>,
    result_typ: Option<RcDoc<'a, ()>>,
) -> RcDoc<'a, ()> {
    make_paren(
        RcDoc::as_string("{ code ")
            .append(expr)
            // .append(" } ")
            // .append(RcDoc::as_string(" #with _")) // ltac:(ssprove_valid'_2)
            .append(RcDoc::as_string(" } :"))
            .append(RcDoc::space())
            .append(RcDoc::as_string("code "))
            .append(match location_vars {
                Some(a) => a,
                None => RcDoc::as_string("_"),
            })
            .append(RcDoc::as_string(" [interface] "))
            .append(match result_typ {
                Some(a) => a,
                None => RcDoc::as_string("_"),
            }),
    )
}

fn bind_code<'a>(
    expr: RcDoc<'a, ()>,
    early_return_typ: Option<EarlyReturnType>,
    typ: Option<BaseTyp>,
    fun_pat: RcDoc<'a, ()>,
    fun_body: RcDoc<'a, ()>,
    smv_total: ScopeMutableVars,
) -> RcDoc<'a, ()> {
    let local_vars_total = fset_from_scope(smv_total.clone());

    // let early_return_args = match typ {
    //     Some(x) => get_result_or_option(x),
    //     None => None,
    // };

    RcDoc::as_string("bnd( ")
        .append(match early_return_typ.clone() {
            Some(EarlyReturnType::Result(_, (c, _))) => {
                RcDoc::as_string("ChoiceEqualityMonad.result_bind_code ")
                    .append(translate_base_typ(c))
            }
            Some(EarlyReturnType::Option(_)) => {
                RcDoc::as_string("ChoiceEqualityMonad.option_bind_code")
            }
            None => RcDoc::as_string("_"),
        })
        .append(RcDoc::as_string(" , "))
        .append(match typ {
            Some(typ) => translate_base_typ(typ),
            None => RcDoc::as_string("_"),
        })
        .append(RcDoc::as_string(" , "))
        .append(match early_return_typ.clone() {
            Some(EarlyReturnType::Result((a, _), _)) | Some(EarlyReturnType::Option((a, _))) => {
                translate_base_typ(a)
            }
            None => RcDoc::as_string("_"),
        })
        .append(RcDoc::as_string(" , "))
        .append(local_vars_total.clone())
        .append(RcDoc::as_string(")"))
        .append(RcDoc::space())
        .append(fun_pat)
        .append(RcDoc::space())
        .append(RcDoc::as_string("⇠"))
        .append(RcDoc::line())
        .append(make_paren(expr))
        .append(RcDoc::space())
        .append(RcDoc::as_string("in"))
        .append(RcDoc::line())
        .append(fun_body)
}

fn translate_constructor<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    RcDoc::as_string(enum_name.string)
}

fn translate_enum_name<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    translate_toplevel_ident(enum_name)
}

fn translate_enum_case_name<'a>(
    enum_name: BaseTyp,
    case_name: TopLevelIdent,
    explicit: bool,
) -> RcDoc<'a> {
    match enum_name {
        BaseTyp::Named(name, opts) => match opts {
            None => translate_constructor(case_name),
            Some(tyvec) => if explicit && tyvec.len() != 0 {
                RcDoc::as_string("@")
            } else {
                RcDoc::nil()
            }
            .append(translate_constructor(case_name))
            .append(
                if (name.0).string == "Option" || (name.0).string == "Result" {
                    RcDoc::nil()
                } else {
                    RcDoc::as_string("(")
                        .append(translate_toplevel_ident(name.0))
                        .append(RcDoc::as_string(")"))
                },
            )
            .append(if explicit && tyvec.len() != 0 {
                RcDoc::space().append(RcDoc::intersperse(
                    tyvec.into_iter().map(|(x, _)| translate_base_typ(x)),
                    RcDoc::space(),
                ))
            } else {
                RcDoc::nil()
            }),
        },
        _ => panic!("should not happen"),
    }
}

pub(crate) fn translate_base_typ<'a>(tau: BaseTyp) -> RcDoc<'a, ()> {
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
        BaseTyp::Named((ident, _span), None) => translate_ident(Ident::TopLevel(ident)),
        BaseTyp::Named((ident, _span), Some(args)) if ident.string == "Result" => make_paren(
            translate_ident(Ident::TopLevel(ident))
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter()
                        .rev()
                        .map(|arg| translate_base_typ(arg.0.clone())),
                    RcDoc::space(),
                )),
        ),
        BaseTyp::Named((ident, _span), Some(args)) => make_paren(
            translate_ident(Ident::TopLevel(ident))
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter().map(|arg| translate_base_typ(arg.0.clone())),
                    RcDoc::space(),
                )),
        ),
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

pub(crate) fn translate_typ<'a>((_, (tau, _)): Typ) -> RcDoc<'a, ()> {
    translate_base_typ(tau)
}

fn translate_literal<'a>(lit: Literal) -> RcDoc<'a, ()> {
    match lit {
        Literal::Unit => RcDoc::as_string("(tt : unit_ChoiceEquality)"),
        Literal::Bool(true) => RcDoc::as_string("(true : bool_ChoiceEquality)"),
        Literal::Bool(false) => RcDoc::as_string("(false : bool_ChoiceEquality)"),
        Literal::Int128(x) => RcDoc::as_string(format!("@repr U128 {}", x)),
        Literal::UInt128(x) => RcDoc::as_string(format!("@repr U128 {}", x)),
        Literal::Int64(x) => RcDoc::as_string(format!("@repr U64 {}", x)),
        Literal::UInt64(x) => RcDoc::as_string(format!("@repr U64 {}", x)),
        Literal::Int32(x) => RcDoc::as_string(format!("@repr U32 {}", x)),
        Literal::UInt32(x) => RcDoc::as_string(format!("@repr U32 {}", x)),
        Literal::Int16(x) => RcDoc::as_string(format!("@repr U16 {}", x)),
        Literal::UInt16(x) => RcDoc::as_string(format!("@repr U16 {}", x)),
        Literal::Int8(x) => RcDoc::as_string(format!("@repr U8 {}", x)),
        Literal::UInt8(x) => RcDoc::as_string(format!("@repr U8 {}", x)),
        Literal::Isize(x) => RcDoc::as_string(format!("isize {}", x)),
        Literal::Usize(x) => RcDoc::as_string(format!("usize {}", x)),
        Literal::Str(msg) => RcDoc::as_string(format!("\"{}\"", msg)),
    }
}

fn translate_pattern_tick<'a>(p: Pattern) -> RcDoc<'a, ()> {
    match p {
        // If the pattern is a tuple, expand it
        Pattern::Tuple(_) => RcDoc::as_string("'").append(translate_pattern(p)),
        _ => translate_pattern(p),
    }
}
fn translate_pattern<'a>(p: Pattern) -> RcDoc<'a, ()> {
    match p {
        Pattern::SingleCaseEnum(name, inner_pat) => {
            translate_enum_case_name(BaseTyp::Named(name.clone(), None), name.0.clone(), false)
                .append(RcDoc::space())
                .append(make_paren(translate_pattern(inner_pat.0)))
        }
        Pattern::IdentPat(x, _m) => translate_ident(x.clone()),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => make_tuple(pats.into_iter().map(|(pat, _)| translate_pattern(pat))),
    }
}

/// Returns the func name, as well as additional arguments to add when calling
/// the function in Coq
fn translate_func_name<'a>(
    prefix: Option<Spanned<BaseTyp>>,
    name: Ident,
    top_ctx: &'a TopLevelContext,
    mut args: Vec<RcDoc<'a, ()>>,
    args_ty: Vec<BaseTyp>,
    inline: bool,
) -> (
    RcDoc<'a, ()>,
    Vec<RcDoc<'a, ()>>,
    Option<BaseTyp>,
    (Vec<RcDoc<'a, ()>>, Vec<RcDoc<'a, ()>>),
) {
    match prefix.clone() {
        None => {
            let name = translate_ident(name.clone());
            match format!("{}", name.pretty(0)).as_str() {
                // In this case, we're trying to apply a secret
                // int constructor. The value it is applied to is
                // a public integer of the same kind. So in Coq, that
                // will amount to a classification operation
                // TODO: may need to add type annotation here
                x @ ("uint128" | "uint64" | "uint32" | "uint16" | "uint8" | "int128" | "int64"
                | "int32" | "int16" | "int8") => (
                    RcDoc::as_string(if inline { "secret_pure" } else { "secret" }),
                    vec![],
                    Some(match x {
                        "uint128" => BaseTyp::UInt128,
                        "uint64" => BaseTyp::UInt64,
                        "uint32" => BaseTyp::UInt32,
                        "uint16" => BaseTyp::UInt16,
                        "uint8" => BaseTyp::UInt8,
                        "int128" => BaseTyp::Int128,
                        "int64" => BaseTyp::Int64,
                        "int32" => BaseTyp::Int32,
                        "int16" => BaseTyp::Int16,
                        "int8" => BaseTyp::Int8,
                        _ => panic!("Should not happen"),
                    }),
                    (vec![], args),
                ),
                _ => (name, vec![], None, (vec![], args)), // TODO: is None correct?
            }
        }
        Some((prefix, _)) => {
            let (module_name, prefix_info) =
                translate_prefix_for_func_name(prefix.clone(), top_ctx);

            let mut result_typ = None;

            let func_ident = translate_ident(name.clone());
            let mut additional_args = Vec::new();

            let mut args_ass = Vec::new();

            // We add the modulo value for nat_mod

            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                (NAT_MODULE, "from_literal") | (NAT_MODULE, "pow2") => {
                    match &prefix_info {
                        FuncPrefix::NatMod(modulo, _) => {
                            if modulo == "unknown" {
                                additional_args.push(RcDoc::as_string("_"));
                            } else {
                                additional_args.push(RcDoc::as_string(format!("0x{}", modulo)));
                            }

                            result_typ = Some(prefix.clone());
                        }
                        _ => panic!(), // should not happen
                    }
                }
                _ => (),
            };
            // And the encoding length for certain nat_mod related function
            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                (NAT_MODULE, "to_public_byte_seq_le") | (NAT_MODULE, "to_public_byte_seq_be") => {
                    match &prefix_info {
                        FuncPrefix::NatMod(_, encoding_bits) => additional_args
                            .push(RcDoc::as_string(format!("{}", (encoding_bits + 7) / 8))),
                        _ => panic!(), // should not happen
                    }
                }
                _ => (),
            };

            // And decoding
            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                (NAT_MODULE, "from_byte_seq_le") | (NAT_MODULE, "from_byte_seq_be") => {
                    match &prefix_info {
                        FuncPrefix::NatMod(_modulo, _) => {
                            result_typ = Some(prefix.clone());
                        }
                        _ => panic!(), // should not happen
                    }
                }
                _ => (),
            };

            // Then the default value for seqs
            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                (ARRAY_MODULE, "new_")
                | (SEQ_MODULE, "new_")
                | (ARRAY_MODULE, "from_slice")
                | (ARRAY_MODULE, "from_slice_range") => {
                    match &prefix_info {
                        FuncPrefix::Array(_, bt) | FuncPrefix::Seq(bt) => {
                            additional_args.push(
                                RcDoc::as_string("default : ")
                                    .append(translate_base_typ(bt.clone())),
                            );
                        }
                        _ => panic!(), // should not happen
                    }
                }
                _ => (),
            };

            // Handle everything with the SeqTrait.
            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                m @ ((ARRAY_MODULE, "from_slice")
                | (ARRAY_MODULE, "concat")
                | (ARRAY_MODULE, "from_slice_range")
                | (ARRAY_MODULE, "set_chunk")
                | (ARRAY_MODULE, "update_slice")
                | (ARRAY_MODULE, "update")
                | (ARRAY_MODULE, "update_start")
                | (ARRAY_MODULE, "from_seq")
                | (SEQ_MODULE, "from_slice")
                | (SEQ_MODULE, "concat")
                | (SEQ_MODULE, "from_slice_range")
                | (SEQ_MODULE, "set_chunk")
                | (SEQ_MODULE, "set_exact_chunk")
                | (SEQ_MODULE, "update_slice")
                | (SEQ_MODULE, "update")
                | (SEQ_MODULE, "update_start")
                | (SEQ_MODULE, "from_seq")
                | (SEQ_MODULE, "from_public_seq")
                | (NAT_MODULE, "from_byte_seq_le")
                | (NAT_MODULE, "from_byte_seq_be")
                | (NAT_MODULE, "to_public_byte_seq_le")
                | (NAT_MODULE, "to_public_byte_seq_be")) => {
                    // position in arg list (does not count self)
                    let position = match m {
                        (ARRAY_MODULE, "from_slice")
                        | (ARRAY_MODULE, "concat")
                        | (ARRAY_MODULE, "from_slice_range")
                        | (ARRAY_MODULE, "update_start")
                        | (ARRAY_MODULE, "from_seq")
                        | (SEQ_MODULE, "from_slice")
                        | (SEQ_MODULE, "concat")
                        | (SEQ_MODULE, "from_slice_range")
                        | (SEQ_MODULE, "update_start")
                        | (SEQ_MODULE, "from_seq")
                        | (SEQ_MODULE, "from_public_seq")
                        | (NAT_MODULE, "from_byte_seq_le")
                        | (NAT_MODULE, "from_byte_seq_be")
                        | (NAT_MODULE, "to_public_byte_seq_le")
                        | (NAT_MODULE, "to_public_byte_seq_be") => 0,
                        (ARRAY_MODULE, "update")
                        | (SEQ_MODULE, "update")
                        | (ARRAY_MODULE, "update_slice")
                        | (SEQ_MODULE, "update_slice") => 1,
                        (ARRAY_MODULE, "set_chunk")
                        | (SEQ_MODULE, "set_chunk")
                        | (SEQ_MODULE, "set_exact_chunk") => 2,
                        _ => panic!(),
                    };

                    let ty = match args_ty[position].clone() {
                        BaseTyp::Named(p, _) => match top_ctx.typ_dict.get(&p.0) {
                            Some(x) => x.0 .1 .0.clone(),
                            None => args_ty[position].clone(),
                        },
                        _ => args_ty[position].clone(),
                    };

                    if let BaseTyp::Array(_, base_ty) = ty {
                        let temp_name = Ident::Local(LocalIdent {
                            id: fresh_codegen_id(),
                            name: String::from("temp"),
                            mutable: false,
                        });
                        let temp_ass: RcDoc<'a, ()> = make_let_binding(
                            Pattern::IdentPat(temp_name.clone(), false),
                            Some(translate_base_typ(BaseTyp::Seq(base_ty))),
                            RcDoc::as_string("array_to_seq (")
                                .append(args[position].clone())
                                .append(RcDoc::as_string(")")),
                            !inline,
                        );
                        args_ass.push(temp_ass);

                        args[position] = translate_ident(temp_name);
                    }
                }
                _ => (),
            };

            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                // Then we add the size for arrays
                (ARRAY_MODULE, "new_")
                | (ARRAY_MODULE, "from_seq")
                | (ARRAY_MODULE, "from_slice")
                | (ARRAY_MODULE, "from_slice_range") => {
                    match &prefix_info {
                        FuncPrefix::Array(ArraySize::Ident(s), _) => {
                            additional_args.push(translate_ident(Ident::TopLevel(s.clone())))
                        }
                        FuncPrefix::Array(ArraySize::Integer(i), _) => {
                            if *i == 0 {
                                additional_args.push(RcDoc::as_string("_"))
                            } else {
                                additional_args.push(RcDoc::as_string(format!("{}", i)))
                            }
                        }
                        FuncPrefix::Seq(_) => {
                            // This is the Seq case, should be alright
                            ()
                        }
                        _ => panic!(), // should not happen
                    }
                }
                _ => (),
            }
            (
                module_name
                    .clone()
                    .append(RcDoc::as_string("_"))
                    .append(func_ident.clone()),
                additional_args,
                result_typ,
                (args_ass, args),
            )
        }
    }
}

fn translate_expression<'a>(
    e: Expression,
    top_ctx: &'a TopLevelContext,
    inline: bool,
) -> (Vec<RcDoc<'a, ()>>, RcDoc<'a, ()>) {
    match e {
        Expression::Binary((op, _), e1, e2, op_typ) => {
            let e1 = e1.0;
            let e2 = e2.0;

            let (ass_e1, trans_e1) = translate_expression(e1, top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2, top_ctx, inline);

            let mut ass = Vec::new();
            ass.extend(ass_e1);
            ass.extend(ass_e2);

            let temp_name = Ident::Local(LocalIdent {
                id: fresh_codegen_id(),
                name: String::from("temp"),
                mutable: false,
            });
            let temp_ass: RcDoc<'a, ()> = make_let_binding(
                Pattern::IdentPat(temp_name.clone(), false),
                None,
                make_paren(trans_e1)
                    .append(RcDoc::space())
                    .append(translate_binop(op, op_typ.as_ref().unwrap(), top_ctx))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .group(),
                !inline,
            );
            ass.push(temp_ass);

            (ass, translate_ident(temp_name))
        }
        //todo
        Expression::MatchWith(arg, arms) => {
            let (ass_arg_0, trans_arg_0) = translate_expression(arg.0, top_ctx, inline);

            let (ass_e1_0_iter, trans_e1_0_iter): (Vec<_>, Vec<_>) = arms
                .into_iter()
                .map(|(enum_name, case_name, payload, e1)| {
                    let (ass_e1, trans_e1) = translate_expression(e1.0, top_ctx, inline);
                    (ass_e1, (enum_name, case_name, payload, trans_e1))
                })
                .unzip();

            let mut ass = Vec::new();
            ass.extend(ass_arg_0);
            ass.extend(ass_e1_0_iter.into_iter().fold(Vec::new(), |mut v, x| {
                v.extend(x);
                v
            }));

            (
                ass,
                RcDoc::as_string("match")
                    .append(RcDoc::space())
                    .append(trans_arg_0)
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("with"))
                    .append(RcDoc::line())
                    .append(RcDoc::intersperse(
                        trans_e1_0_iter.into_iter().map(
                            |(enum_name, case_name, payload, trans_e1_0)| {
                                RcDoc::as_string("|")
                                    .append(RcDoc::space())
                                    .append(translate_enum_case_name(
                                        enum_name.clone(),
                                        case_name.0.clone(),
                                        false,
                                    ))
                                    .append(match &payload {
                                        Some(payload) => RcDoc::space()
                                            .append(translate_pattern(payload.0.clone())),
                                        None => RcDoc::nil(),
                                    })
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string("=>"))
                                    .append(RcDoc::space())
                                    .append(trans_e1_0)
                            },
                        ),
                        RcDoc::line(),
                    ))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("end")),
            )
        }
        //todo
        Expression::EnumInject(enum_name, case_name, payload) => {
            let (ass, trans) = match payload {
                None => (Vec::new(), RcDoc::nil()),
                Some(payload) => {
                    let (ass, trans) = translate_expression(*payload.0.clone(), top_ctx, inline);
                    (ass, RcDoc::space().append(make_paren(trans)))
                }
            };

            (
                ass,
                translate_enum_case_name(enum_name.clone(), case_name.0.clone(), true)
                    .append(trans),
            )
        }
        Expression::InlineConditional(cond, e_t, e_f) => {
            let cond = cond.0;
            let e_t = e_t.0;
            let e_f = e_f.0;

            let (ass_cond, trans_cond) = translate_expression(cond, top_ctx, inline);
            let (ass_e_t, trans_e_t) = translate_expression(e_t, top_ctx, inline);
            let (ass_e_f, trans_e_f) = translate_expression(e_f, top_ctx, inline);

            let mut ass = Vec::new();
            ass.extend(ass_cond);
            ass.extend(ass_e_t);
            ass.extend(ass_e_f);

            (
                ass,
                make_paren(
                    RcDoc::as_string("if")
                        .append(RcDoc::space())
                        .append(make_paren(trans_cond))
                        .append(RcDoc::as_string(":bool_ChoiceEquality"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("then"))
                        .append(RcDoc::space())
                        .append(make_paren(trans_e_t))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("else"))
                        .append(RcDoc::space())
                        .append(make_paren(trans_e_f)),
                )
                .group(),
            )
        }
        Expression::Unary(op, e1, op_typ) => {
            let e1 = e1.0;

            let (ass, trans) = translate_expression(e1, top_ctx, inline);

            (
                ass,
                translate_unop(op, op_typ.as_ref().unwrap().clone())
                    .append(RcDoc::space())
                    .append(make_paren(trans))
                    .group(),
            )
        }
        Expression::Lit(lit) => (Vec::new(), translate_literal(lit.clone())),
        Expression::Tuple(es) => {
            let (ass_iter, trans_iter): (Vec<_>, Vec<_>) = es
                .into_iter()
                .map(|(e, _)| {
                    let (ass, trans) = translate_expression(e, top_ctx, inline);
                    (ass, trans)
                })
                .unzip();

            (
                ass_iter.into_iter().fold(Vec::new(), |mut v, x| {
                    v.extend(x);
                    v
                }),
                {
                    let iter = trans_iter.into_iter();
                    match &iter.size_hint().1 {
                        Some(0) => RcDoc::as_string("tt"),
                        Some(1) => {
                            RcDoc::intersperse(iter, RcDoc::as_string(",").append(RcDoc::line()))
                                .group()
                        } // TODO: just get next, instead of using intersperse for a single element
                        _ => RcDoc::as_string("prod_ce").append(
                            RcDoc::as_string("(")
                                .append(
                                    RcDoc::line_()
                                        .append(RcDoc::intersperse(
                                            iter,
                                            RcDoc::as_string(",").append(RcDoc::line()),
                                        ))
                                        .group()
                                        .nest(2),
                                )
                                .append(RcDoc::line_())
                                .append(RcDoc::as_string(")"))
                                .group(),
                        ),
                    }
                },
            )
        }
        Expression::Named(p) => (Vec::new(), translate_ident(p.clone())),
        Expression::FuncCall(prefix, name, args, arg_types) => {
            let (ass_arg_iter, trans_arg_iter): (Vec<_>, Vec<_>) = args
                .clone()
                .into_iter()
                .map(|((arg, _), _)| {
                    let (ass, trans) = translate_expression(arg, top_ctx, inline);
                    (ass, trans)
                })
                .unzip();

            let (func_name, additional_args, func_ret_ty, (trans_arg_ass, trans_arg_iter)) =
                translate_func_name(
                    prefix.clone(),
                    Ident::TopLevel(name.0.clone()),
                    top_ctx,
                    trans_arg_iter,
                    arg_types.unwrap(),
                    inline,
                );
            let total_args = args.len() + additional_args.len();

            let mut ass: Vec<RcDoc<'a, ()>> = Vec::new();
            ass.extend(ass_arg_iter.into_iter().fold(Vec::new(), |mut v, x| {
                v.extend(x);
                v
            }));
            ass.extend(trans_arg_ass);

            let fun_expr = func_name
                // We append implicit arguments first
                .append(RcDoc::concat(
                    additional_args
                        .into_iter()
                        .map(|arg| RcDoc::space().append(make_paren(arg))),
                ))
                // Then the explicit arguments
                .append(RcDoc::concat(
                    trans_arg_iter
                        .into_iter()
                        .map(|trans_arg| RcDoc::space().append(make_paren(trans_arg))),
                ))
                .append(if total_args == 0 {
                    RcDoc::space() //.append(RcDoc::as_string("()"))
                } else {
                    RcDoc::nil()
                });

            let temp_name = Ident::Local(LocalIdent {
                id: fresh_codegen_id(),
                name: String::from("temp"),
                mutable: false,
            });

            let temp_ass: RcDoc<'a, ()> = make_let_binding(
                Pattern::IdentPat(temp_name.clone(), false),
                func_ret_ty.map(|ret_ty| translate_base_typ(ret_ty)),
                fun_expr,
                !inline,
            );
            ass.push(temp_ass);

            (ass, translate_ident(temp_name))
        }
        Expression::MethodCall(sel_arg, sel_typ, (f, _), args, arg_types) => {
            let (ass_sel_arg_0_0, trans_sel_arg_0_0) =
                translate_expression((sel_arg.0).0, top_ctx, inline);

            let (ass_arg_iter, trans_arg_iter): (Vec<_>, Vec<_>) = args
                .into_iter()
                .map(|((arg, _), _)| {
                    let (ass, trans) = translate_expression(arg, top_ctx, inline);
                    (ass, trans)
                })
                .unzip();

            let ass_arg = ass_arg_iter.into_iter().fold(Vec::new(), |mut v, x| {
                v.extend(x);
                v
            });

            let mut ass = Vec::new();
            ass.extend(ass_sel_arg_0_0);
            ass.extend(ass_arg);

            let (func_name, additional_args, func_ret_ty, (trans_args_ass, trans_arg_iter)) =
                translate_func_name(
                    sel_typ.clone().map(|x| x.1),
                    Ident::TopLevel(f.clone()),
                    top_ctx,
                    trans_arg_iter,
                    arg_types.unwrap(),
                    inline,
                );

            ass.extend(trans_args_ass);

            let arg_trans = // Then the self argument
                    make_paren(trans_sel_arg_0_0)
                        // And finally the rest of the arguments
                        .append(RcDoc::concat(trans_arg_iter.into_iter().map(
                        |trans_arg| {
                            RcDoc::space().append(make_paren(trans_arg))
                        },
                    )));

            // Ignore "clone" // TODO: is this correct?
            if f.string == "clone" {
                (ass, arg_trans)
            } else {
                let method_call_expr = func_name // We append implicit arguments first
                    .append(RcDoc::concat(
                        additional_args
                            .into_iter()
                            .map(|arg| RcDoc::space().append(make_paren(arg))),
                    ))
                    .append(RcDoc::space())
                    .append(arg_trans.clone())
                    .append(match func_ret_ty.clone() {
                        Some(ret_ty) => RcDoc::as_string(" : ").append(translate_base_typ(ret_ty)),
                        None => RcDoc::nil(),
                    });

                let temp_name = Ident::Local(LocalIdent {
                    id: fresh_codegen_id(),
                    name: String::from("temp"),
                    mutable: false,
                });

                let temp_ass: RcDoc<'a, ()> = make_let_binding(
                    Pattern::IdentPat(temp_name.clone(), false),
                    func_ret_ty.clone().map(|ret_ty| translate_base_typ(ret_ty)),
                    method_call_expr,
                    !inline,
                );
                ass.push(temp_ass);

                (ass, translate_ident(temp_name))
            }
        }
        Expression::ArrayIndex(x, e2, typ) => {
            let e2 = e2.0;
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);

            let (ass_e2, trans_e2) = translate_expression(e2, top_ctx, inline);

            let mut ass = Vec::new();
            ass.extend(ass_e2);

            let temp_name = Ident::Local(LocalIdent {
                id: fresh_codegen_id(),
                name: String::from("temp"),
                mutable: false,
            });
            let temp_ass: RcDoc<'a, ()> = make_let_binding(
                Pattern::IdentPat(temp_name.clone(), false),
                None,
                array_or_seq
                    .append(RcDoc::as_string("_index"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_ident(x.0.clone())))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2)),
                !inline,
            );
            ass.push(temp_ass);

            (ass, translate_ident(temp_name))
        }
        // Expression::NewArray(_array_name, inner_ty, args) => {
        Expression::NewArray(_array_name, inner_ty, args) => {
            let inner_ty = inner_ty.unwrap();
            // inner_ty is the type of the cell elements
            // TODO: do the case when _array_name is None (the Seq case)
            let (ass_iter, trans_iter): (Vec<_>, Vec<_>) = args
                .into_iter()
                .map(|(e, _)| {
                    let (ass, trans) = translate_expression(e.clone(), top_ctx, inline);
                    (ass, trans)
                })
                .unzip();

            let ass = ass_iter.into_iter().fold(Vec::new(), |mut v, x| {
                v.extend(x);
                v
            });
            let trans = make_list(trans_iter);

            (
                ass,
                match _array_name {
                    // Seq case
                    None => trans,
                    Some(_) =>
                    // Array case
                    {
                        RcDoc::as_string(format!("{}_from_list", ARRAY_MODULE))
                            .append(RcDoc::space())
                            .append(translate_base_typ(inner_ty.clone()))
                            .append(RcDoc::space())
                            .append(trans)
                    }
                },
            )
        }
        Expression::IntegerCasting(x, new_t, old_t) => {
            let old_t = old_t.unwrap();
            match old_t {
                BaseTyp::Usize | BaseTyp::Isize => {
                    let new_t_doc = match &new_t.0 {
                        BaseTyp::UInt8 => RcDoc::as_string("pub_u8"),
                        BaseTyp::UInt16 => RcDoc::as_string("pub_u16"),
                        BaseTyp::UInt32 => RcDoc::as_string("pub_u32"),
                        BaseTyp::UInt64 => RcDoc::as_string("pub_u64"),
                        BaseTyp::UInt128 => RcDoc::as_string("pub_u128"),
                        BaseTyp::Usize => RcDoc::as_string("usize"),
                        BaseTyp::Int8 => RcDoc::as_string("pub_i8"),
                        BaseTyp::Int16 => RcDoc::as_string("pub_i16"),
                        BaseTyp::Int32 => RcDoc::as_string("pub_i32"),
                        BaseTyp::Int64 => RcDoc::as_string("pub_i64"),
                        BaseTyp::Int128 => RcDoc::as_string("pub_i28"),
                        BaseTyp::Isize => RcDoc::as_string("isize"),
                        _ => panic!(), // should not happen
                    };
                    let (ass_x, trans_x) = translate_expression(x.0.clone(), top_ctx, inline);
                    (
                        ass_x,
                        new_t_doc.append(RcDoc::space()).append(make_paren(trans_x)),
                    )
                }
                _ => {
                    let new_t_doc = match &new_t.0 {
                        BaseTyp::UInt8 => String::from("uint8"),
                        BaseTyp::UInt16 => String::from("uint16"),
                        BaseTyp::UInt32 => String::from("uint32"),
                        BaseTyp::UInt64 => String::from("uint64"),
                        BaseTyp::UInt128 => String::from("uint128"),
                        BaseTyp::Usize => String::from("uint32"),
                        BaseTyp::Int8 => String::from("int8"),
                        BaseTyp::Int16 => String::from("int16"),
                        BaseTyp::Int32 => String::from("int32"),
                        BaseTyp::Int64 => String::from("int64"),
                        BaseTyp::Int128 => String::from("int128"),
                        BaseTyp::Isize => String::from("int32"),
                        BaseTyp::Named((TopLevelIdent { string: s, .. }, _), None) => s.clone(),
                        _ => panic!(), // should not happen
                    };
                    let _secret = match &new_t.0 {
                        BaseTyp::Named(_, _) => true,
                        _ => false,
                    };
                    let (ass_x, trans_x) =
                        translate_expression(x.as_ref().0.clone(), top_ctx, inline);
                    (
                        ass_x,
                        RcDoc::as_string("@cast _")
                            .append(RcDoc::space())
                            .append(new_t_doc)
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("_"))
                            .append(RcDoc::space())
                            .append(make_paren(trans_x))
                            .group(),
                    )
                }
            }
        }
    }
}

fn translate_statements<'a>(
    mut statements: Iter<Spanned<Statement>>,
    top_ctx: &'a TopLevelContext,
    inline: bool,
    smv: ScopeMutableVars,
) -> RcDoc<'a, ()> {
    let s = match statements.next() {
        None => return RcDoc::nil(),
        Some(s) => s.clone(),
    };

    match s.0 {
        Statement::LetBinding((pat, _), typ, (expr, _), question_mark) => {
            let (ass_expr, trans_expr) = translate_expression(expr.clone(), top_ctx, inline);
            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = match question_mark {
                Some((smv_bind, early_return_typ)) => bind_code(
                    code_block_wrap(
                        ass_expr
                            .into_iter()
                            .fold(RcDoc::nil(), |rc, x| rc.append(x))
                            .append(RcDoc::as_string("@ret _ ").append(make_paren(trans_expr))),
                        None, // Some(smv.clone()),
                        None,
                    ),
                    None,
                    typ.map(|((_, (x, _)), _)| x), // = early_return_typ
                    match pat.clone() {
                        Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
                        _ => RcDoc::nil(),
                    }
                    .append(translate_pattern_tick(pat.clone())),
                    code_block_wrap(trans_stmt, None, None),
                    smv.clone(),
                ),
                None => if let Pattern::IdentPat(_i, true) = pat.clone() {
                    // TODO: encapsulate in scope its own varaible
                    make_put_binding(
                        pat.clone(),
                        typ.map(|(typ, _)| translate_typ(typ)),
                        ass_expr
                            .into_iter()
                            .fold(RcDoc::nil(), |rc, x| rc.append(x))
                            .append(
                                RcDoc::as_string("ret")
                                    .append(RcDoc::space())
                                    .append(make_paren(trans_expr)),
                            ),
                    )
                } else {
                    make_let_binding(
                        pat.clone(),
                        typ.map(|(typ, _)| translate_typ(typ)),
                        ass_expr
                            .into_iter()
                            .fold(RcDoc::nil(), |rc, x| rc.append(x))
                            .append(
                                RcDoc::as_string("ret")
                                    .append(RcDoc::space())
                                    .append(make_paren(trans_expr)),
                            ),
                        !inline,
                    )
                }
                .append(trans_stmt),
            };

            expr
        }
        Statement::Reassignment((x, _), (e1, _), question_mark) => {
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let trans_e1 = make_paren(
                ass_e1
                    .into_iter()
                    .fold(RcDoc::nil(), |rc, x| rc.append(x))
                    .append(
                        RcDoc::as_string("ret")
                            .append(RcDoc::space())
                            .append(make_paren(trans_e1)),
                    ),
            );

            let expr = match question_mark {
                Some((smv_bind, early_return_typ)) => bind_code(
                    trans_e1,
                    early_return_typ,
                    None,
                    translate_ident(x.clone()),
                    code_block_wrap(trans_stmt, None, None),
                    smv.clone(),
                ),
                None => make_put_binding(Pattern::IdentPat(x.clone(), true), None, trans_e1)
                    .append(RcDoc::hardline())
                    .append(trans_stmt),
            };

            expr
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.clone().unwrap(), top_ctx);
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2.clone(), top_ctx, inline);

            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = match question_mark {
                Some((smv_bind, early_return_typ)) => bind_code(
                    trans_e2,
                    early_return_typ,
                    typ.map(|(_, (x, _))| x),
                    RcDoc::as_string("_temp"),
                    make_let_binding(
                        Pattern::IdentPat(x.clone(), false),
                        None,
                        (ass_e1.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                            .append(ass_e2.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                            .append(
                                RcDoc::as_string("ret")
                                    .append(RcDoc::space())
                                    .append(make_paren(
                                        array_or_seq
                                            .append(RcDoc::as_string("_upd"))
                                            .append(RcDoc::space())
                                            .append(translate_ident(x.clone()))
                                            .append(RcDoc::space())
                                            .append(make_paren(trans_e1))
                                            .append(RcDoc::space())
                                            .append(RcDoc::as_string("_temp")),
                                    )),
                            ),
                        false,
                    )
                    .append(RcDoc::hardline())
                    .append(trans_stmt),
                    smv.clone(),
                ),
                None => {
                    let array_upd_payload =
                        RcDoc::as_string("ret")
                            .append(RcDoc::space())
                            .append(make_paren(
                                array_or_seq
                                    .append(RcDoc::as_string("_upd"))
                                    .append(RcDoc::space())
                                    .append(translate_ident(x.clone()))
                                    .append(RcDoc::space())
                                    .append(make_paren(trans_e1))
                                    .append(RcDoc::space())
                                    .append(make_paren(trans_e2)),
                            ));

                    make_let_binding(
                        Pattern::IdentPat(x.clone(), false),
                        typ.clone().map(|(_, (x, _))| translate_base_typ(x)),
                        (ass_e1.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                            .append(ass_e2.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                            .append(array_upd_payload),
                        !inline,
                    )
                    .append(RcDoc::hardline())
                    .append(trans_stmt)
                }
            };

            expr
        }

        Statement::ReturnExp(e1, t1) => {
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);

            ass_e1
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(RcDoc::as_string("@ret "))
                .append(make_paren(match t1 {
                    Some((_, (x, _))) => translate_base_typ(x),
                    None => RcDoc::as_string("_"),
                }))
                .append(RcDoc::space())
                .append(make_paren(trans_e1))
        }
        Statement::Conditional((cond, _), (mut b1, _), b2, mutated) => {
            let mutated_info = mutated.unwrap();
            let pat = Pattern::Tuple(
                mutated_info
                    .vars
                    .0
                    .iter()
                    .sorted()
                    .map(|i| {
                        (
                            Pattern::IdentPat(Ident::Local(i.clone()), false),
                            DUMMY_SP.into(),
                        )
                    })
                    .collect(),
            );
            let b1_question_mark = *b1.contains_question_mark.as_ref().unwrap();
            let b2_question_mark = match &b2 {
                None => false,
                Some(b2) => *b2.0.contains_question_mark.as_ref().unwrap(),
            };
            let either_blocks_contains_question_mark = b1_question_mark || b2_question_mark;
            b1.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                mutated_info.early_return_type.clone(),
                if either_blocks_contains_question_mark
                // b1_question_mark
                {
                    Some(ScopeMutableVars::new())
                } else {
                    None
                },
            ));

            let (ass_cond, trans_cond) = translate_expression(cond.clone(), top_ctx, inline);
            let block_1 = translate_block(b1.clone(), true, top_ctx, inline);

            let else_expr = match b2.clone() {
                None => translate_statements(
                    vec![add_ok_if_result(
                        mutated_info.stmt.clone(),
                        mutated_info.early_return_type.clone(),
                        if either_blocks_contains_question_mark
                        // b1_question_mark
                        {
                            Some(b1.mutable_vars.clone())
                        } else {
                            None
                        },
                    )].iter(),
                    top_ctx,
                    inline,
                    smv.clone(),
                ),
                Some((mut b2, _)) => {
                    b2.stmts.push(add_ok_if_result(
                        mutated_info.stmt.clone(),
                        mutated_info.early_return_type.clone(),
                        if either_blocks_contains_question_mark
                        // b2_question_mark
                        {
                            Some(b2.mutable_vars.clone())
                        } else {
                            None
                        },
                    ));

                    let block2_expr = translate_block(b2, true, top_ctx, inline);

                    RcDoc::space().append(make_paren(block2_expr))
                }
            };

            let trans_stmt = translate_statements(statements.clone(), top_ctx, inline, smv.clone());

            let either_expr = if either_blocks_contains_question_mark {
                // let local_vars_bind_1 = fset_from_scope(b1.mutable_vars.clone());
                // let local_vars_bind_2 = match b2.clone() {
                //     Some((b2, _)) => fset_from_scope(b2.mutable_vars.clone()),
                //     _ => RcDoc::as_string("fset.fset0"),
                // };
                // let local_vars_fun = fset_from_scope(smv.clone());

                let expr = RcDoc::as_string(
                    "if", // "ifbnd"
                )
                // .append(RcDoc::as_string(" (A := _) (B := "))
                // .append(match mutated_info.early_return_type.clone() {
                //     Some(EarlyReturnType::Result((a, _), _))
                //     | Some(EarlyReturnType::Option((a, _))) => translate_base_typ(a),
                //     None => RcDoc::as_string("_"),
                // })
                // .append(RcDoc::as_string(") (H_bind_code := "))
                // .append(match mutated_info.early_return_type.clone() {
                //     Some(EarlyReturnType::Result(_, (c, _))) => {
                //         RcDoc::as_string("ChoiceEqualityMonad.result_bind_code ")
                //             .append(translate_base_typ(c))
                //     }
                //     Some(EarlyReturnType::Option(_)) => {
                //         RcDoc::as_string("ChoiceEqualityMonad.option_bind_code")
                //     }
                //     None => RcDoc::as_string("_"),
                // })
                // .append(RcDoc::as_string(") (Lx := "))
                // .append(local_vars_bind_1.clone())
                // .append(RcDoc::as_string(") (Ly := "))
                // .append(local_vars_bind_2.clone())
                // .append(RcDoc::as_string(") (L2 := "))
                // .append(local_vars_fun.clone())
                // .append(RcDoc::as_string(") (it1 := _) (it2 := _)"))
                // .append(RcDoc::space())
                .append(RcDoc::space())
                .append(trans_cond)
                .append(RcDoc::space())
                .append(RcDoc::as_string(": bool_ChoiceEquality"))
                .append(RcDoc::line())
                .append(RcDoc::as_string("then"))
                .append(RcDoc::space())
                .append(code_block_wrap(block_1.clone(), None, None))
                .append(RcDoc::line())
                .append(RcDoc::as_string("else"))
                .append(RcDoc::space())
                .append(code_block_wrap(else_expr, None, None))
                .append(RcDoc::space());
                // // .append(RcDoc::as_string(">> "))
                // .append(RcDoc::as_string("(fun"))
                // .append(RcDoc::space())
                // .append(translate_pattern_tick(pat))
                // .append(RcDoc::space())
                // .append(RcDoc::as_string("=>"))
                // .append(RcDoc::line())
                // .append(code_block_wrap(trans_stmt, None, None))
                // .append(RcDoc::as_string(")"))

                bind_code(
                    expr,
                    mutated_info.early_return_type.clone(),
                    None,
                    translate_pattern_tick(pat),
                    code_block_wrap(trans_stmt, None, None),
                    smv.clone(),
                )
            } else {
                let expr = RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(trans_cond.clone())
                    .append(RcDoc::as_string(":bool_ChoiceEquality"))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("then"))
                    .append(RcDoc::space())
                    .append(make_paren(block_1.clone()))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("else"))
                    .append(RcDoc::space())
                    .append(else_expr);

                make_let_binding(pat, None, expr, !inline)
                    .append(RcDoc::hardline())
                    .append(trans_stmt)
            };

            ass_cond
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(either_expr)
        }
        Statement::ForLoop(x, (e1, _), (e2, _), (mut b, _)) => {
            let mutated_info = b.mutated.clone().unwrap();
            // TODO: handle question_mark
            let b_question_mark = *b.contains_question_mark.as_ref().unwrap();
            // b.stmts.push((
            //     Statement::ReturnExp(
            //         Expression::Lit(Literal::Unit),
            //         Some((
            //             (Borrowing::Consumed, DUMMY_SP.into()),
            //             (BaseTyp::Unit, DUMMY_SP.into()),
            //         )),
            //     ),
            //     DUMMY_SP.into(),
            // ));
            b.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                mutated_info.early_return_type.clone(),
                if b_question_mark {
                    Some(b.mutable_vars.clone())
                } else {
                    None
                },
            ));

            let mut_tuple = {
                // if there is only one element, just print the identifier instead of making a tuple
                if mutated_info.vars.0.len() == 1 {
                    match mutated_info.vars.0.iter().next() {
                        None => Pattern::WildCard,
                        Some(i) => Pattern::IdentPat(Ident::Local(i.clone()), false),
                    }
                }
                // print as tuple otherwise
                else {
                    Pattern::Tuple(
                        mutated_info
                            .vars
                            .0
                            .iter()
                            .sorted()
                            .map(|i| {
                                (
                                    Pattern::IdentPat(Ident::Local(i.clone()), false),
                                    DUMMY_SP.into(),
                                )
                            })
                            .collect(),
                    )
                }
            };

            // TODO: Add ass_e1 and ass_e2 correctly to loop expression !
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2.clone(), top_ctx, inline);

            let block_expr = translate_block(b.clone(), true, top_ctx, inline);
            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = if b_question_mark {
                let local_vars_bind = fset_from_scope(b.mutable_vars.clone());
                let local_vars_fun = fset_from_scope(smv.clone());

                let loop_expr = RcDoc::as_string("foldi_bind_code")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .append(RcDoc::space())
                    .append(make_paren(
                        RcDoc::as_string("lift_to_code (ChoiceEqualityMonad.ret ")
                            .append(match mut_tuple.clone() {
                                Pattern::Tuple(_) => RcDoc::as_string("prod_ce")
                                    .append(translate_pattern(mut_tuple.clone())),
                                _ => translate_pattern(mut_tuple.clone()),
                            })
                            .append(RcDoc::as_string(")")), // TODO: Ok only when result
                    ))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(fun"))
                    .append(RcDoc::space())
                    .append(match x {
                        Some((x, _)) => translate_ident(x.clone()),
                        None => RcDoc::as_string("_"),
                    })
                    .append(RcDoc::space())
                    .append(translate_pattern_tick(mut_tuple.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(block_expr)
                    .append(RcDoc::as_string(")"));

                bind_code(
                    loop_expr,
                    mutated_info.early_return_type.clone(),
                    // mutated_info.early_return_type.clone().map(|x| match x {
                    //     EarlyReturnType::Result((a, _), _) | EarlyReturnType::Option((a, _)) => a,
                    // })
                    None,
                    if mutated_info.vars.0.iter().len() == 0 {
                        RcDoc::as_string("_")
                    } else {
                        RcDoc::as_string("'").append(translate_pattern(mut_tuple.clone()))
                    }, // TODO: Issue here with patterns (eg. 'tt)
                    code_block_wrap(trans_stmt, None, None),
                    smv.clone(),
                )
            } else {
                let loop_expr = RcDoc::as_string("foldi")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .append(RcDoc::space())
                    .append(translate_pattern(mut_tuple.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(fun"))
                    .append(RcDoc::space())
                    .append(match x {
                        Some((x, _)) => translate_ident(x.clone()),
                        None => RcDoc::as_string("_"),
                    })
                    .append(RcDoc::space())
                    .append(make_paren(
                        translate_pattern(mut_tuple.clone())
                            .append(RcDoc::as_string(" : "))
                            // .append(translate_typ(tau.clone()))
                            .append(RcDoc::as_string("_")),
                    ))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(block_expr)
                    .append(RcDoc::as_string(")"))
                    // .append(RcDoc::as_string(";;"))
                    .group()
                    .nest(2);

                make_let_binding(mut_tuple.clone(), None, loop_expr, !inline)
                    .append(RcDoc::hardline())
                    .append(trans_stmt)
            };

            ass_e1
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(ass_e2.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                .append(expr)
        }
    }
    // .group()
}

fn list_of_loc_vars<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    let mut all = smvars.external_vars.clone();
    all.extend(locals.clone());

    RcDoc::as_string("[")
        .append(RcDoc::intersperse(
            all.into_iter()
                .map(|(i, _)| i)
                .sorted()
                .map(|i| translate_ident(i.clone()).append("_loc")),
            RcDoc::space()
                .append(RcDoc::as_string(";"))
                .append(RcDoc::space()),
        ))
        .append(RcDoc::as_string("]"))
}

pub(crate) fn fset_from_scope<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    let mut all = smvars.external_vars.clone();
    all.extend(locals.clone());

    if all.len() == 0 {
        RcDoc::as_string("fset.fset0")
    } else {
        RcDoc::as_string("CEfset ").append(make_paren(list_of_loc_vars(smvars)))
    }
}

fn locations_from_scope<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    RcDoc::intersperse(
        locals.into_iter().map(|(i, typ)| {
            make_definition(
                translate_ident(i.clone()).append("_loc"),
                Some(RcDoc::as_string("ChoiceEqualityLocation")),
                make_paren(
                    match typ {
                        Some(typ) => translate_typ(typ),
                        None => RcDoc::as_string("_"),
                    }
                    .append(RcDoc::space())
                    // .append(RcDoc::as_string(": choice_type")).append(RcDoc::space())
                    .append(RcDoc::as_string(";"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(fresh_codegen_id()))
                    .append(RcDoc::as_string("%nat")),
                ),
            )
        }),
        RcDoc::line(),
    )
}

pub(crate) fn fset_and_locations<'a>(smvars: ScopeMutableVars) -> (RcDoc<'a, ()>, RcDoc<'a, ()>) {
    (
        fset_from_scope(smvars.clone()),
        locations_from_scope(smvars.clone()),
    )
}

fn translate_block<'a>(
    b: Block,
    omit_extra_unit: bool,
    top_ctx: &'a TopLevelContext,
    inline: bool,
) -> RcDoc<'a, ()> {
    let mut statements = b.stmts;
    match (&b.return_typ, omit_extra_unit) {
        (None, _) => panic!(), // should not happen,
        (Some(((Borrowing::Consumed, _), (BaseTyp::Unit, _))), false) => {
            statements.push((
                Statement::ReturnExp(Expression::Lit(Literal::Unit), b.return_typ),
                DUMMY_SP.into(),
            ));
        }
        (Some(_), _) => (),
    }

    let trans_stmt =
        translate_statements(statements.iter(), top_ctx, inline, b.mutable_vars.clone());
    let local_vars = fset_from_scope(b.mutable_vars);

    code_block_wrap(trans_stmt.group(), Some(make_paren(local_vars)), None)
}

pub(crate) fn translate_item<'a>(
    item: DecoratedItem,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    match &item.item {
        Item::FnDecl((f, _), sig, (b, _)) => {
            let block_exprs = translate_block(b.clone(), false, top_ctx, false);
            let (block_vars, block_var_loc_defs) = fset_and_locations(sig.mutable_vars.clone());

            block_var_loc_defs
                .append(RcDoc::line())
                .append(RcDoc::as_string("Program"))
                .append(RcDoc::space())
                .append(make_definition(translate_ident(Ident::TopLevel(f.clone()))
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
                            }),
                            Some(RcDoc::as_string("code")
                            .append(RcDoc::space())
                            .append(make_paren(block_vars))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("[interface]"))
                            .append(RcDoc::space())
                            .append(make_paren(
                                RcDoc::as_string("@ct")
                                    .append(RcDoc::space())
                                    .append(make_paren(translate_base_typ(sig.ret.0.clone())))
                            ))),
                                block_exprs.group()))
                .append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))

        },
        Item::EnumDecl(name, cases) => RcDoc::as_string("Inductive")
            .append(RcDoc::space())
            .append(translate_enum_name(name.0.clone()))
            .append(RcDoc::space())
            .append(RcDoc::as_string(":="))
            .append(RcDoc::line())
            .append(RcDoc::intersperse(
                cases.into_iter().map(|(case_name, case_typ)| {
                    let name_ty = BaseTyp::Named(name.clone(), None);
                    RcDoc::as_string("|")
                        .append(RcDoc::space())
                        .append(translate_enum_case_name(name_ty, case_name.0.clone(), false))
                        .append(match case_typ {
                            None => RcDoc::space()
                                .append(RcDoc::as_string(":"))
                                .append(RcDoc::space())
                                .append(translate_enum_name(name.0.clone())),
                            Some(case_typ) => RcDoc::space()
                                .append(RcDoc::as_string(":"))
                                .append(RcDoc::space())
                                .append(translate_base_typ(case_typ.0.clone()))
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("->"))
                                .append(RcDoc::space())
                                .append(translate_enum_name(name.0.clone())),
                        })
                }),
                RcDoc::line(),
            ))
            .append(RcDoc::as_string("."))
            .append(if item.tags.0.contains(&"PartialEq".to_string()) {
                RcDoc::hardline()
                    .append(RcDoc::hardline())
                    .append(RcDoc::as_string("Definition"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("eqb_"))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(x y : "))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::as_string(")"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("bool_ChoiceEquality"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .append(RcDoc::line())
                    .append(
                        RcDoc::as_string("match x with")
                            .append(RcDoc::line())
                            .append(RcDoc::intersperse(
                                cases.into_iter().map(|(case_name, case_typ)| {
                                    let name_ty = BaseTyp::Named(name.clone(), None);
                                    RcDoc::as_string("|")
                                        .append(RcDoc::space())
                                        .append(translate_enum_case_name(
                                            name_ty.clone(),
                                            case_name.0.clone(), false,
                                        ))
                                        .append(RcDoc::space())
                                        .append(match case_typ {
                                            None => RcDoc::nil(),
                                            Some(_) => RcDoc::as_string("a").append(RcDoc::space()),
                                        })
                                        .append(RcDoc::as_string("=>"))
                                        .append(RcDoc::line())
                                        .append(
                                            RcDoc::as_string("match y with")
                                                .append(RcDoc::line())
                                                .append(RcDoc::as_string("|"))
                                                .append(RcDoc::space())
                                                .append(translate_enum_case_name(
                                                    name_ty.clone(),
                                                    case_name.0.clone(), false,
                                                ))
                                                .append(match case_typ {
                                                    None => RcDoc::as_string("=> true"),
                                                    Some(_) => RcDoc::space()
                                                        .append(RcDoc::as_string("b"))
                                                        .append(RcDoc::space())
                                                        .append(RcDoc::as_string("=> a =.? b")),
                                                })
                                                .append(RcDoc::line())
                                                .append(match &cases.into_iter().size_hint().1 {
                                                    Some(0) => RcDoc::nil(),
                                                    Some(1) => RcDoc::nil(),
                                                    _ => RcDoc::as_string("| _ => false")
                                                        .append(RcDoc::line()),
                                                })
                                                .append(RcDoc::as_string("end")),
                                        )
                                        .group()
                                        .nest(4)
                                }),
                                RcDoc::line(),
                            ))
                            .append(RcDoc::line())
                            .append("end.")
                            .nest(3),
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append(RcDoc::as_string("Definition"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("eqb_leibniz_"))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(x y : "))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::as_string(") :"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("eqb_"))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("x y = true <-> x = y."))
                    .append(RcDoc::hardline())
                    .append(
                        RcDoc::as_string("Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.")
                    )
                    .append(RcDoc::hardline())
                    .append(RcDoc::hardline())
                    .append(RcDoc::as_string("Instance"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("eq_dec_"))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("EqDec ("))
                    .append(translate_enum_name(name.0.clone()))
                    .append(RcDoc::as_string(") :="))
                    .append(RcDoc::hardline())
                    .append(
                        RcDoc::as_string("Build_EqDec (")
                            .append(translate_enum_name(name.0.clone()))
                            .append(RcDoc::as_string(") (eqb_"))
                            .append(translate_enum_name(name.0.clone()))
                            .append(RcDoc::as_string(") (eqb_leibniz_"))
                            .append(translate_enum_name(name.0.clone()))
                            .append(RcDoc::as_string(")."))
                            .nest(2)
                    )
                    .append(RcDoc::hardline())
            } else {
                RcDoc::nil()
            })
            ,
        Item::ArrayDecl(name, size, cell_t, index_typ) => {
            let (ass_size_0, trans_size_0) = translate_expression(size.0.clone(), top_ctx, false);
            make_definition(translate_ident(Ident::TopLevel(name.0.clone())), None, ass_size_0.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(
                RcDoc::line()
                    .append(RcDoc::as_string("nseq"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_base_typ(cell_t.0.clone())))
                    .append(RcDoc::space())
                    .append(make_paren(trans_size_0.clone()))
                    .group()
                    .nest(2),
            ))
            .append(match index_typ {
                None => RcDoc::nil(),
                Some(index_typ) => RcDoc::hardline()
                    .append(RcDoc::hardline())
                    .append(make_definition(
                        translate_ident(Ident::TopLevel(index_typ.0.clone())),
                        None,
                        RcDoc::as_string("nat_mod")
                            .append(RcDoc::space())
                            .append(make_paren(trans_size_0.clone())),
                    ))
                    .append(RcDoc::hardline())
                    .append(make_uint_size_coercion(translate_ident(Ident::TopLevel(
                        index_typ.0.clone(),
                    )))),
            })
        }
        Item::ConstDecl(name, ty, e) => {
            let (ass_e_0, trans_e_0) = translate_expression(e.0.clone(), top_ctx, true);
            make_definition(translate_ident(Ident::TopLevel(name.0.clone())), Some(make_paren(translate_base_typ(ty.0.clone()))), ass_e_0.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)).append(make_paren(trans_e_0))
            )
        },
        Item::NaturalIntegerDecl(nat_name, _secrecy, canvas_size, info) => {
            let canvas_size = match &canvas_size.0 {
                Expression::Lit(Literal::Usize(size)) => size,
                _ => panic!(), // should not happen by virtue of typchecking
            };
            let canvas_size_bytes = RcDoc::as_string(format!("{}", (canvas_size + 7) / 8));
            (match info {
                Some((canvas_name, _modulo)) => make_definition(translate_ident(Ident::TopLevel(canvas_name.0.clone())), None, RcDoc::as_string("nseq")
                            .append(RcDoc::space())
                            .append(make_paren(translate_base_typ(BaseTyp::UInt8)))
                            .append(RcDoc::space())
                            .append(make_paren(canvas_size_bytes.clone()))
                    )
                    .append(RcDoc::hardline()),
                None => RcDoc::nil(),
            })
            .append(
                make_definition(translate_ident(Ident::TopLevel(nat_name.0.clone())), None, RcDoc::as_string("nat_mod")
                            .append(RcDoc::space())
                            .append(match info {
                                Some((_, modulo)) => RcDoc::as_string(format!("0x{}", &modulo.0)),
                                None => RcDoc::as_string(format!("pow2 {}", canvas_size)),
                            })
                    )

            )
        }
        Item::ImportedCrate((TopLevelIdent { string: kr, .. }, _)) => {
            RcDoc::as_string(format!(
            "Require Import {}.",
                str::replace(&kr.to_title_case(), " ", "_"),
            ))
        }
        // Aliases are translated to Coq Notations
        Item::AliasDecl((ident, _), (ty, _)) => {
            RcDoc::as_string("Notation")
                .append(RcDoc::space())
                .append(RcDoc::as_string("\"'"))
                .append(translate_ident(Ident::TopLevel(ident.clone())))
                .append(RcDoc::as_string("'\""))
                .append(RcDoc::space())
                .append(RcDoc::as_string(":= ("))
                .append(translate_base_typ(ty.clone()))
                .append(RcDoc::as_string(") : hacspec_scope."))

        }
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
         Open Scope bool_scope.\n\
         \n\
         Require Import ChoiceEquality.\n\
         Require Import LocationUtility.\n\
         Require Import Hacspec_Lib_Comparable.\n\
         Require Import Hacspec_Lib_Pre.\n\
         Require Import Hacspec_Lib.\n\
         \n\
         Open Scope hacspec_scope.\n\n\
         Obligation Tactic := try timeout 8 solve_ssprove_obligations.\n",
    )
    .unwrap();
    translate_program(p, top_ctx).render(width, &mut w).unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
