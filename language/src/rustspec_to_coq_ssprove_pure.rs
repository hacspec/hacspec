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

pub(crate) fn make_definition_inner<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    (pat.clone()
        .append(match typ.clone() {
            None => RcDoc::nil(),
            Some(tau) => RcDoc::space()
                .append(RcDoc::as_string(":"))
                .append(RcDoc::space())
                .append(tau),
        })
        .group())
    .append(RcDoc::space())
    .append(RcDoc::as_string(":="))
    .group()
    .append(RcDoc::line().append(expr.group()))
    .nest(2)
    .append(RcDoc::as_string("."))
}

pub(crate) fn make_let_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
    toplevel: bool,
) -> RcDoc<'a, ()> {
    RcDoc::as_string(if toplevel { "Definition" } else { "let" })
        .append(RcDoc::space())
        .append(
            pat.clone()
                .append(match typ.clone() {
                    None => RcDoc::nil(),
                    Some(tau) => RcDoc::space()
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(tau),
                })
                .group(),
        )
        .append(RcDoc::space())
        .append(RcDoc::as_string(":="))
        .group()
        .append(RcDoc::line().append(expr.group()))
        .nest(2)
        .append(if toplevel {
            RcDoc::as_string(".")
        } else {
            RcDoc::space()
                .append(RcDoc::as_string("in"))
                .append(RcDoc::space())
        })
}

fn make_uint_size_coercion<'a>(pat: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
    RcDoc::as_string("Definition")
        .append(RcDoc::space())
        .append(RcDoc::as_string("uint_size_in_"))
        .append(pat.clone())
        .append(RcDoc::as_string("(n : uint_size) : "))
        .append(pat.clone())
        .append(RcDoc::space())
        .append(RcDoc::as_string(":= int_in_nat_mod n."))
        .append(RcDoc::line())
        .append(RcDoc::as_string("Coercion "))
        .append(RcDoc::as_string("uint_size_in_"))
        .append(pat.clone())
        .append(RcDoc::as_string(" : uint_size >-> "))
        .append(pat.clone())
        .append(RcDoc::as_string("."))
}

fn make_tuple<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
    let iter = args.into_iter();
    match &iter.size_hint().1 {
        Some(0) => RcDoc::as_string("tt"),
        _ => RcDoc::as_string("(")
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
    }
}

fn make_list<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
    RcDoc::as_string("[")
        .append(
            RcDoc::line_()
                .append(RcDoc::intersperse(
                    args.into_iter(),
                    RcDoc::as_string(";").append(RcDoc::line()),
                ))
                .group()
                .nest(2),
        )
        .append(RcDoc::line_())
        .append(RcDoc::as_string("]"))
        .group()
}

fn make_typ_tuple<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
    RcDoc::as_string("(")
        .append(
            RcDoc::line_()
                .append(RcDoc::intersperse(
                    args.into_iter(),
                    RcDoc::space()
                        .append(RcDoc::as_string("'×"))
                        .append(RcDoc::line()),
                ))
                .group()
                .nest(2),
        )
        .append(RcDoc::line_())
        .append(RcDoc::as_string(")"))
        .group()
}

fn make_paren<'a>(e: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
    RcDoc::as_string("(")
        .append(RcDoc::softline_().append(e).group().nest(2))
        .append(RcDoc::as_string(")"))
        .group()
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
        BaseTyp::Named((ident, _span), None) => translate_ident(Ident::TopLevel(ident)),
        BaseTyp::Named((ident, _span), Some(args)) => make_paren(if ident.string == "Result" {
            translate_ident(Ident::TopLevel(ident))
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter()
                        .rev()
                        .map(|arg| translate_base_typ(arg.0.clone())),
                    RcDoc::space(),
                ))
        } else {
            translate_ident(Ident::TopLevel(ident))
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter().map(|arg| translate_base_typ(arg.0.clone())),
                    RcDoc::space(),
                ))
        }),
        BaseTyp::Variable(id) => RcDoc::as_string(format!("t{}", id.0)),
        BaseTyp::Tuple(args) => {
            if args.len() == 0 {
                RcDoc::as_string("unit")
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

/// Returns the func name, as well as additional arguments to add when calling
/// the function in Coq
pub(crate) fn translate_func_name<'a>(
    prefix: Option<Spanned<BaseTyp>>,
    name: Ident,
    top_ctx: &'a TopLevelContext,
    args_ty: Vec<BaseTyp>,
) -> (
    RcDoc<'a, ()>,
    Vec<RcDoc<'a, ()>>,
    Option<BaseTyp>,
    Vec<(RcDoc<'a, ()>, RcDoc<'a, ()>)>,
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
                    RcDoc::as_string("secret"),
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
                    vec![],
                ),
                _ => (name, vec![], None, vec![]), // TODO: is None correct?
            }
        }
        Some((prefix, _)) => {
            let (module_name, prefix_info) =
                translate_prefix_for_func_name(prefix.clone(), top_ctx);

            let mut result_typ = None;

            let func_ident = translate_ident(name.clone());
            let mut additional_args = Vec::new();

            let mut extra_info = Vec::new();

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

                    if let BaseTyp::Array(..) = ty {
                        while extra_info.len() <= position {
                            extra_info.push((RcDoc::nil(), RcDoc::nil()))
                        }
                        extra_info.insert(
                            position,
                            (RcDoc::as_string("array_to_seq ("), RcDoc::as_string(")")),
                        );
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
                extra_info,
            )
        }
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
        Pattern::IdentPat(x, _mutable) => translate_ident(x.clone()),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => make_tuple(pats.into_iter().map(|(pat, _)| translate_pattern(pat))),
    }
}

fn translate_expression<'a>(e: Expression, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match e {
        Expression::Binary((op, _), e1, e2, op_typ) => {
            let e1 = e1.0;
            let e2 = e2.0;
            // RcDoc::as_string("is_pure")
            // .append(
            make_paren(
                make_paren(translate_expression(e1, top_ctx))
                    .append(RcDoc::space())
                    .append(translate_binop(op, op_typ.as_ref().unwrap(), top_ctx))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e2, top_ctx)))
                    .group(),
            ) // )
        }
        //todo
        Expression::MatchWith(arg, arms) => RcDoc::as_string("match")
            .append(RcDoc::space())
            .append(translate_expression(arg.0, top_ctx))
            .append(RcDoc::space())
            .append(RcDoc::as_string("with"))
            .append(RcDoc::line())
            .append(RcDoc::intersperse(
                arms.into_iter().map(|(enum_name, case_name, payload, e1)| {
                    RcDoc::as_string("|")
                        .append(RcDoc::space())
                        .append(translate_enum_case_name(
                            enum_name.clone(),
                            case_name.0.clone(),
                            false,
                        ))
                        .append(match &payload {
                            Some(payload) => {
                                RcDoc::space().append(translate_pattern(payload.0.clone()))
                            }
                            None => RcDoc::nil(),
                        })
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("=>"))
                        .append(RcDoc::space())
                        .append(translate_expression(e1.0, top_ctx))
                }),
                RcDoc::line(),
            ))
            .append(RcDoc::line())
            .append(RcDoc::as_string("end")),
        //todo
        Expression::EnumInject(enum_name, case_name, payload) => {
            translate_enum_case_name(enum_name.clone(), case_name.0.clone(), true).append(
                match payload {
                    None => RcDoc::nil(),
                    Some(payload) => RcDoc::space().append(make_paren(translate_expression(
                        *payload.0.clone(),
                        top_ctx,
                    ))),
                },
            )
        }
        Expression::InlineConditional(cond, e_t, e_f) => {
            let cond = cond.0;
            let e_t = e_t.0;
            let e_f = e_f.0;
            make_paren(
                RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(cond, top_ctx)))
                    .append(RcDoc::as_string(":bool_ChoiceEquality"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("then"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e_t, top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("else"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e_f, top_ctx))),
            )
            .group()
        }
        Expression::Unary(op, e1, op_typ) => {
            let e1 = e1.0;
            translate_unop(op, op_typ.as_ref().unwrap().clone())
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1, top_ctx)))
                .group()
        }
        Expression::Lit(lit) => translate_literal(lit.clone()),
        Expression::Tuple(es) if es.len() <= 1 => make_tuple(
            es.into_iter()
                .map(|(e, _)| translate_expression(e, top_ctx)),
        ),
        Expression::Tuple(es) => {
            let iter = es
                .into_iter()
                .map(|(e, _)| translate_expression(e, top_ctx));
            match &iter.size_hint().1 {
                Some(0) => RcDoc::as_string("tt"),
                Some(1) => RcDoc::intersperse(iter, RcDoc::nil()), // TODO: less hacky solution
                _ => RcDoc::as_string("prod_ce(")
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
            }
        }
        Expression::Named(p) => translate_ident(p.clone()),
        Expression::FuncCall(prefix, name, args, arg_types) => {
            let (func_name, additional_args, func_ret_ty, extra_info) = translate_func_name(
                prefix.clone(),
                Ident::TopLevel(name.0.clone()),
                top_ctx,
                arg_types.unwrap(),
            );

            let total_args = args.len() + additional_args.len();
            func_name
                // We append implicit arguments first
                .append(RcDoc::concat(
                    additional_args
                        .into_iter()
                        .map(|arg| RcDoc::space().append(make_paren(arg))),
                ))
                // Then the explicit arguments
                .append(RcDoc::concat(args.into_iter().enumerate().map(
                    |(i, ((arg, _), _))| {
                        RcDoc::space().append(make_paren(if i < extra_info.len() {
                            let (pre_arg, post_arg) = extra_info[i].clone();
                            pre_arg
                                .clone()
                                .append(translate_expression(arg, top_ctx))
                                .append(post_arg.clone())
                        } else {
                            translate_expression(arg, top_ctx)
                        }))
                    },
                )))
                .append(if total_args == 0 {
                    RcDoc::space() //.append(RcDoc::as_string("()"))
                } else {
                    RcDoc::nil()
                })
            // .append(match func_ret_ty {
            //     Some(ret_ty) => RcDoc::as_string(" : ").append(translate_base_typ(ret_ty)),
            //     None => RcDoc::nil(),
            // })
        }
        Expression::MethodCall(sel_arg, sel_typ, (f, _), args, arg_types) => {
            // Ignore "clone" // TODO: is this correct?
            if f.string == "clone" {
                // Then the self argument
                make_paren(translate_expression((sel_arg.0).0, top_ctx))
                    // And finally the rest of the arguments
                    .append(RcDoc::concat(args.into_iter().map(|((arg, _), _)| {
                        RcDoc::space().append(make_paren(translate_expression(arg, top_ctx)))
                    })))
            } else {
                let (func_name, additional_args, func_ret_ty, extra_info) = translate_func_name(
                    sel_typ.clone().map(|x| x.1),
                    Ident::TopLevel(f.clone()),
                    top_ctx,
                    arg_types.unwrap(),
                );
                func_name // We append implicit arguments first
                    .append(RcDoc::concat(
                        additional_args
                            .into_iter()
                            .map(|arg| RcDoc::space().append(make_paren(arg))),
                    ))
                    .append(RcDoc::space())
                    // Then the self argument
                    .append(make_paren(translate_expression((sel_arg.0).0, top_ctx)))
                    // And finally the rest of the arguments
                    .append(RcDoc::concat(args.into_iter().enumerate().map(
                        |(i, ((arg, _), _))| {
                            RcDoc::space().append(make_paren(if i < extra_info.len() {
                                let (pre_arg, post_arg) = extra_info[i].clone();
                                pre_arg
                                    .clone()
                                    .append(translate_expression(arg, top_ctx))
                                    .append(post_arg.clone())
                            } else {
                                translate_expression(arg, top_ctx)
                            }))
                        },
                    )))
                // .append(match func_ret_ty {
                //     Some(ret_ty) => RcDoc::as_string(" : ").append(translate_base_typ(ret_ty)),
                //     None => RcDoc::nil(),
                // })
            }
        }
        Expression::ArrayIndex(x, e2, typ) => {
            let e2 = e2.0;
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);
            array_or_seq
                .append(RcDoc::as_string("_index"))
                .append(RcDoc::space())
                .append(make_paren(translate_ident(x.0.clone())))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2, top_ctx)))
        }
        // Expression::NewArray(_array_name, inner_ty, args) => {
        Expression::NewArray(_array_name, inner_ty, args) => {
            let inner_ty = inner_ty.unwrap();
            // inner_ty is the type of the cell elements
            // TODO: do the case when _array_name is None (the Seq case)
            match _array_name {
                // Seq case
                None => make_list(
                    args.into_iter()
                        .map(|(e, _)| translate_expression(e.clone(), top_ctx)),
                ),
                Some(_) =>
                // Array case
                {
                    RcDoc::as_string(format!("{}_from_list", ARRAY_MODULE))
                        .append(RcDoc::space())
                        .append(translate_base_typ(inner_ty.clone()))
                        .append(RcDoc::space())
                        .append(make_list(args.into_iter().map(|(e, _)| {
                            make_paren(translate_expression(e, top_ctx))
                                .append(RcDoc::as_string(" : "))
                                .append(translate_base_typ(inner_ty.clone()))
                        })))
                }
            }
        }
        Expression::IntegerCasting(x, new_t, old_t) => {
            let old_t = old_t.unwrap();
            match old_t {
                BaseTyp::Usize | BaseTyp::Isize => {
                    (match &new_t.0 {
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
                    })
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(x.0.clone(), top_ctx)))
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
                    RcDoc::as_string("@cast _")
                        .append(RcDoc::space())
                        .append(new_t_doc)
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("_"))
                        .append(RcDoc::space())
                        .append(make_paren(translate_expression(
                            x.as_ref().0.clone(),
                            top_ctx,
                        )))
                        .group()
                }
            }
        }
    }
}

// TODO: Remove code duplication !
// taken from rustspec_to_fstar
fn add_ok_if_result(
    stmt: Statement,
    early_return_type: Fillable<EarlyReturnType>,
    question_mark: bool,
) -> Spanned<Statement> {
    (
        match early_return_type {
            Some(ert) => {
                if question_mark {
                    // If b has an early return, then we must prefix the returned
                    // mutated variables by Ok or Some
                    match stmt {
                        Statement::ReturnExp(e, typ) => Statement::ReturnExp(
                            Expression::EnumInject(
                                BaseTyp::Named(
                                    (
                                        TopLevelIdent {
                                            string: match ert {
                                                EarlyReturnType::Option(_) => "Option",
                                                EarlyReturnType::Result(_, _) => "Result",
                                            }
                                            .to_string(),
                                            kind: TopLevelIdentKind::Type,
                                        },
                                        DUMMY_SP.into(),
                                    ),
                                    None,
                                ),
                                (
                                    TopLevelIdent {
                                        string: match ert {
                                            EarlyReturnType::Option(_) => "Some",
                                            EarlyReturnType::Result(_, _) => "Ok",
                                        }
                                        .to_string(),
                                        kind: TopLevelIdentKind::EnumConstructor,
                                    },
                                    DUMMY_SP.into(),
                                ),
                                Some((Box::new(e.clone()), DUMMY_SP.into())),
                            ),
                            typ,
                        ),
                        _ => panic!("should not happen"),
                    }
                } else {
                    stmt.clone()
                }
            }
            _ => stmt.clone(),
        },
        DUMMY_SP.into(),
    )
}

fn translate_statements<'a>(
    mut statements: Iter<Spanned<Statement>>,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    let s = match statements.next() {
        None => return RcDoc::nil(),
        Some(s) => s.clone(),
    };
    match s.0 {
        Statement::LetBinding((pat, _), typ, (expr, _), question_mark) => {
            if question_mark.is_some() {
                match pat.clone() {
                    Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
                    _ => RcDoc::nil(),
                }
                .append(RcDoc::space())
                .append(translate_pattern_tick(pat.clone()))
                .append(RcDoc::space())
                .append(RcDoc::as_string("m( _ ) ⇠"))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(expr.clone(), top_ctx)))
                .append(RcDoc::space())
                .append(RcDoc::as_string(";;"))
                .append(RcDoc::line())
                .append(make_paren(translate_statements(statements, top_ctx)))
            } else {
                match pat.clone() {
                    Pattern::SingleCaseEnum(_, _) | Pattern::Tuple(_) => make_let_binding(
                        translate_pattern_tick(pat.clone()),
                        None,
                        translate_expression(expr.clone(), top_ctx).append(match typ.clone() {
                            Some((typ, _)) => RcDoc::as_string(" : ").append(translate_typ(typ)),
                            None => RcDoc::nil(),
                        }),
                        false,
                    ),
                    _ => make_let_binding(
                        translate_pattern_tick(pat.clone()),
                        typ.clone().map(|(typ, _)| translate_typ(typ)),
                        translate_expression(expr.clone(), top_ctx),
                        false,
                    ),
                }
                .append(RcDoc::hardline())
                .append(translate_statements(statements, top_ctx))
            }
        }
        Statement::Reassignment((x, _), _x_typ, (e1, _), question_mark) =>
        //TODO: not yet handled
        {
            if question_mark.is_some() {
                translate_ident(x.clone())
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("m( _ ) ⇠"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(";;"))
                    .append(RcDoc::line())
                    .append(make_paren(translate_statements(statements, top_ctx)))
            } else {
                make_let_binding(
                    translate_ident(x.clone()),
                    None,
                    translate_expression(e1.clone(), top_ctx),
                    false,
                )
                .append(RcDoc::hardline())
                .append(translate_statements(statements, top_ctx))
            }
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);
            if question_mark.is_some() {
                RcDoc::as_string("_temp")
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("m( _ ) ⇠"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e2.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(";;"))
                    .append(RcDoc::line())
                    .append(make_paren(
                        make_let_binding(
                            translate_ident(x.clone()),
                            None,
                            array_or_seq
                                .append(RcDoc::as_string("_upd"))
                                .append(RcDoc::space())
                                .append(translate_ident(x.clone()))
                                .append(RcDoc::space())
                                .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("_temp")),
                            false,
                        )
                        .append(RcDoc::hardline())
                        .append(translate_statements(statements, top_ctx)),
                    ))
            } else {
                let array_upd_payload = array_or_seq
                    .append(RcDoc::as_string("_upd"))
                    .append(RcDoc::space())
                    .append(translate_ident(x.clone()))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e2.clone(), top_ctx)));

                make_let_binding(translate_ident(x.clone()), None, array_upd_payload, false)
                    .append(RcDoc::hardline())
                    .append(translate_statements(statements, top_ctx))
            }
        }

        Statement::ReturnExp(e1, _typ) => translate_expression(e1.clone(), top_ctx),
        Statement::Conditional((cond, _), (mut b1, _), b2, mutated) => {
            let mutated_info = mutated.unwrap();
            let pat = RcDoc::as_string("'").append(make_tuple(
                mutated_info
                    .vars
                    .0
                    .iter()
                    .sorted()
                    .map(|i| translate_ident(Ident::Local(i.clone()))),
            ));
            let b1_question_mark = *b1.contains_question_mark.as_ref().unwrap();
            let b2_question_mark = match &b2 {
                None => false,
                Some(b2) => *b2.0.contains_question_mark.as_ref().unwrap(),
            };
            let either_blocks_contains_question_mark = b1_question_mark || b2_question_mark;
            b1.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                mutated_info.early_return_type.clone(),
                b1_question_mark,
            ));

            if either_blocks_contains_question_mark {
                let block1 = make_paren(translate_block(b1.clone(), true, top_ctx));
                // RcDoc::as_string("let f a :=")
                //     .append(RcDoc::line()) // softline
                //     .append(translate_statements(statements.clone(), top_ctx))
                //     .append(RcDoc::line()) // softline
                //     .append(RcDoc::as_string("in"))
                //     .append(RcDoc::line())
                // .append(
                RcDoc::as_string("ifbnd") // )
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(cond.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(": bool_ChoiceEquality"))
                    .append(RcDoc::line())
                    .append(if b1_question_mark {
                        RcDoc::as_string("thenbnd")
                    } else {
                        RcDoc::as_string("then")
                    })
                    .append(RcDoc::space())
                    .append(block1)
                    .append(RcDoc::line())
                    .append(match b2 {
                        None => RcDoc::as_string("else")
                            .append(RcDoc::space())
                            // .append("f")
                            // .append(RcDoc::space())
                            .append(make_paren(translate_statements(
                                [(mutated_info.stmt.clone(), DUMMY_SP.into())].iter(),
                                top_ctx,
                            ))),
                        Some((mut b2, _)) => {
                            b2.stmts.push(add_ok_if_result(
                                mutated_info.stmt.clone(),
                                mutated_info.early_return_type.clone(),
                                b2_question_mark,
                            ));
                            let block2 = make_paren(translate_block(b2, true, top_ctx));
                            (if b2_question_mark {
                                RcDoc::as_string("elsebnd")
                            } else {
                                RcDoc::as_string("else")
                            })
                            .append(block2)
                        }
                    })
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(">> (fun"))
                    .append(RcDoc::space())
                    .append(pat)
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(translate_statements(statements.clone(), top_ctx))
                    .append(RcDoc::as_string(")"))
            } else {
                let expr = make_paren(
                    make_paren(
                        RcDoc::as_string("if")
                            .append(RcDoc::space())
                            .append(make_paren(translate_expression(cond.clone(), top_ctx)))
                            .append(RcDoc::as_string(":bool_ChoiceEquality"))
                            .append(RcDoc::line())
                            .append(RcDoc::as_string("then"))
                            .append(RcDoc::space())
                            .append(make_paren(translate_block(b1.clone(), true, top_ctx)))
                            .append(RcDoc::line())
                            .append(match b2.clone() {
                                None => RcDoc::as_string("else").append(RcDoc::space()).append(
                                    make_paren(translate_statements(
                                        [(mutated_info.stmt.clone(), DUMMY_SP.into())].iter(),
                                        top_ctx,
                                    )),
                                ),
                                Some((mut b2, _)) => {
                                    b2.stmts.push(add_ok_if_result(
                                        mutated_info.stmt.clone(),
                                        mutated_info.early_return_type.clone(),
                                        b2_question_mark,
                                    ));
                                    RcDoc::as_string("else")
                                        .append(RcDoc::space())
                                        .append(make_paren(translate_block(b2, true, top_ctx)))
                                }
                            }),
                    )
                    .append(RcDoc::as_string(" : T _")),
                );
                make_let_binding(pat, None, expr, false)
                    .append(RcDoc::hardline())
                    .append(translate_statements(statements.clone(), top_ctx))
            }
        }
        Statement::ForLoop(x, (e1, _), (e2, _), (mut b, _)) => {
            let mutated_info = b.mutated.clone().unwrap();
            // TODO: handle question_mark
            let b_question_mark = *b.contains_question_mark.as_ref().unwrap();
            b.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                mutated_info.early_return_type.clone(),
                b_question_mark,
            ));

            let mut_tuple = |prefix: String| -> RcDoc<'a> {
                // if there is only one element, just print the identifier instead of making a tuple
                if mutated_info.vars.0.len() == 1 {
                    match mutated_info.vars.0.iter().next() {
                        None => RcDoc::nil(),
                        Some(i) => translate_ident(Ident::Local(i.clone())),
                    }
                }
                // print as tuple otherwise
                else {
                    RcDoc::as_string(prefix).append(make_tuple(
                        mutated_info
                            .vars
                            .0
                            .iter()
                            .sorted()
                            .map(|i| translate_ident(Ident::Local(i.clone()))),
                    ))
                }
            };
            if b_question_mark {
                let loop_expr = RcDoc::as_string("foldibnd")
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("to"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e2.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("M( _ )"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("for"))
                    .append(RcDoc::space())
                    .append(mut_tuple("prod_ce".to_string()).clone())
                    .append(RcDoc::space())
                    .append(">> (fun")
                    .append(RcDoc::space())
                    .append(match x {
                        Some((x, _)) => translate_ident(x.clone()),
                        None => RcDoc::as_string("_"),
                    })
                    .append(RcDoc::space())
                    .append(mut_tuple("'".to_string()).clone())
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(translate_block(b, true, top_ctx))
                    .append(RcDoc::as_string(")"));

                if mutated_info.vars.0.iter().len() == 0 {
                    // TODO: Issue here with patterns (eg. 'tt)
                    RcDoc::as_string("_")
                } else {
                    mut_tuple("'".to_string()).clone()
                }
                .append(RcDoc::space())
                .append(RcDoc::as_string("m( _ ) ⇠"))
                .append(RcDoc::space())
                .append(make_paren(loop_expr))
                .append(RcDoc::space())
                .append(RcDoc::as_string(";;"))
                .append(RcDoc::line())
                .append(make_paren(translate_statements(statements, top_ctx)))
            } else {
                let loop_expr = RcDoc::as_string("Hacspec_Lib_Pre.foldi") // foldi_both
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(e2.clone(), top_ctx)))
                    .append(RcDoc::space())
                    .append(mut_tuple("".to_string()).clone())
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("(fun"))
                    .append(RcDoc::space())
                    .append(match x {
                        Some((x, _)) => translate_ident(x.clone()),
                        None => RcDoc::as_string("_"),
                    })
                    .append(RcDoc::space())
                    .append(mut_tuple("'".to_string()).clone())
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(translate_block(b, true, top_ctx))
                    .append(RcDoc::as_string(")"))
                    .group()
                    .nest(2);

                make_let_binding(mut_tuple("'".to_string()), None, loop_expr, false)
                    .append(RcDoc::hardline())
                    .append(translate_statements(statements, top_ctx))
            }
        }
    }
    .group()
}

fn translate_block<'a>(
    b: Block,
    omit_extra_unit: bool,
    top_ctx: &'a TopLevelContext,
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
    translate_statements(statements.iter(), top_ctx).group()
}

pub(crate) fn translate_item<'a>(
    item: DecoratedItem,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    match &item.item {
        Item::FnDecl((f, _), sig, (b, _)) => make_let_binding(
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
                        .append(translate_base_typ(sig.ret.0.clone()))
                        .group(),
                ),
            None,
            translate_block(b.clone(), false, top_ctx)
                .append(RcDoc::nil())
                .group(),
            true,
        )
        .append(
            RcDoc::hardline()
                .append(make_let_binding(
                    translate_ident(Ident::TopLevel(f.clone()))
                        .append(RcDoc::as_string("_code"))
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
                                .append(RcDoc::as_string("code fset.fset0 [interface] (@ct "))
                                .append(make_paren(translate_base_typ(sig.ret.0.clone())))
                                .append(RcDoc::as_string(")"))
                                .group(),
                        ),
                    None,
                    RcDoc::as_string("lift_to_code")
                        .append(RcDoc::space())
                        .append(make_paren(
                            translate_ident(Ident::TopLevel(f.clone()))
                                .append(RcDoc::space()
                                        .append(if sig.args.len() > 0 {
                                            RcDoc::intersperse(
                                                sig.args.iter().map(|((x, _), (_, _))| {
                                                    translate_ident(x.clone())
                                                }),
                                                RcDoc::line(),
                                            )
                                        } else {
                                            RcDoc::nil()
                                        })
                                )
                        )),
                    true
                ))),
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
            }),
        Item::ArrayDecl(name, size, cell_t, index_typ) => RcDoc::as_string("Definition")
            .append(RcDoc::space())
            .append(translate_ident(Ident::TopLevel(name.0.clone())))
            .append(RcDoc::space())
            .append(RcDoc::as_string(":="))
            .group()
            .append(
                RcDoc::line()
                    .append(RcDoc::as_string("nseq"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_base_typ(cell_t.0.clone())))
                    .append(RcDoc::space())
                    .append(make_paren(translate_expression(size.0.clone(), top_ctx)))
                    .group()
                    .nest(2),
            )
            .append(RcDoc::as_string("."))
            .append(match index_typ {
                None => RcDoc::nil(),
                Some(index_typ) => RcDoc::hardline()
                    .append(RcDoc::hardline())
                    .append(make_let_binding(
                        translate_ident(Ident::TopLevel(index_typ.0.clone())),
                        None,
                        RcDoc::as_string("nat_mod")
                            .append(RcDoc::space())
                            .append(make_paren(translate_expression(size.0.clone(), top_ctx))),
                        true,
                    ))
                    .append(RcDoc::hardline())
                    .append(make_uint_size_coercion(translate_ident(Ident::TopLevel(
                        index_typ.0.clone(),
                    )))),
            }),
        Item::ConstDecl(name, ty, e) => make_let_binding(
            translate_ident(Ident::TopLevel(name.0.clone())),
            Some(translate_base_typ(ty.0.clone())),
            translate_expression(e.0.clone(), top_ctx),
            true,
        ),
        Item::NaturalIntegerDecl(nat_name, _secrecy, canvas_size, info) => {
            let canvas_size = match &canvas_size.0 {
                Expression::Lit(Literal::Usize(size)) => size,
                _ => panic!(), // should not happen by virtue of typchecking
            };
            let canvas_size_bytes = RcDoc::as_string(format!("usize {}", (canvas_size + 7) / 8));
            (match info {
                Some((canvas_name, _modulo)) => RcDoc::as_string("Definition")
                    .append(RcDoc::space())
                    .append(translate_ident(Ident::TopLevel(canvas_name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .group()
                    .append(
                        RcDoc::line()
                            .append(RcDoc::as_string("nseq"))
                            .append(RcDoc::space())
                            .append(make_paren(translate_base_typ(BaseTyp::UInt8)))
                            .append(RcDoc::space())
                            .append(make_paren(canvas_size_bytes.clone()))
                            .group()
                            .nest(2),
                    )
                    .append(RcDoc::as_string("."))
                    .append(RcDoc::hardline()),
                None => RcDoc::nil(),
            })
            .append(
                RcDoc::as_string("Definition")
                    .append(RcDoc::space())
                    .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .group()
                    .append(
                        RcDoc::line()
                            .append(RcDoc::as_string("nat_mod"))
                            .append(RcDoc::space())
                            .append(match info {
                                Some((_, modulo)) => RcDoc::as_string(format!("0x{}", &modulo.0)),
                                None => RcDoc::as_string(format!("pow2 {}", canvas_size)),
                            })
                            .append(RcDoc::as_string("."))
                            .group()
                            .nest(2),
                    )
                    ,
            )
        }
        Item::ImportedCrate((TopLevelIdent { string: kr, .. }, _)) => {
            if &kr.to_title_case() == "Hacspec Lib" {
                RcDoc::nil()
            } else {
            RcDoc::as_string(format!(
            "Require Import {}.",
                str::replace(&kr.to_title_case(), " ", "_"),
            ))
            }
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
         Set Warnings \"-notation-overridden,-ambiguous-paths\".\n\
         From Crypt Require Import choice_type Package Prelude.\n\
         Import PackageNotation.\n\
         From extructures Require Import ord fset.\n\
         From mathcomp Require Import ssrZ word.\n\
         From Jasmin Require Import word.\n\
         Require Import ChoiceEquality.\n\
         \n\
         From Coq Require Import ZArith.\n\
         Import List.ListNotations.\n\
         Open Scope list_scope.\n\
         Open Scope Z_scope.\n\
         Open Scope bool_scope.\n\
         \n\
         Require Import Hacspec_Lib_Comparable.\n\
         Require Import Hacspec_Lib_Pre.\n\
         \n\
         Open Scope hacspec_scope.\n\n",
    )
    .unwrap();
    translate_program(p, top_ctx).render(width, &mut w).unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
