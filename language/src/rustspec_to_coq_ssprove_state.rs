use crate::name_resolution::{DictEntry, TopLevelContext};
use crate::rustspec::*;
use core::iter::IntoIterator;
use core::slice::Iter;
use heck::TitleCase;
use im::HashSet;
use itertools::Itertools;
use pretty::RcDoc;
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use std::fs::File;
use std::io::Write;
use std::path;

use crate::name_resolution::{FnKey, FnValue};
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

fn make_put_binding<'a>(pat: Pattern, typ: Option<BaseTyp>, expr: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
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
    typ: Option<BaseTyp>,
    expr: RcDoc<'a, ()>,
    do_bind: bool,
) -> RcDoc<'a, ()> {
    let mut typed_bound_tuple = None;

    RcDoc::as_string(if do_bind { "" } else { "let" })
        .append(RcDoc::space())
        .append(
            match typ.clone() {
                None => translate_pattern_tick(pat.clone()),
                Some(tau) => match pat.clone() {
                    // If the pattern is a tuple, expand it
                    Pattern::Tuple(v) if v.len() > 1 => {
                        if do_bind {
                            let temp_name = translate_ident(Ident::Local(LocalIdent {
                                id: fresh_codegen_id(),
                                name: String::from("temp"),
                                mutable: false,
                            }));
                            typed_bound_tuple = Some(temp_name.clone());
                            temp_name
                        } else {
                            translate_pattern_tick(pat.clone())
                        }
                    }
                    _ => {
                        if do_bind {
                            RcDoc::as_string("'").append(make_paren(
                                translate_pattern(pat.clone())
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string(":"))
                                    .append(RcDoc::space())
                                    .append(translate_base_typ(tau)),
                            ))
                        } else {
                            translate_pattern(pat.clone())
                                .append(RcDoc::space())
                                .append(RcDoc::as_string(":"))
                                .append(RcDoc::space())
                                .append(translate_base_typ(tau))
                        }
                    }
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
                        .append(translate_base_typ(tau)),
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
        .append(match typed_bound_tuple {
            None => RcDoc::nil(),
            Some(temp_name) => make_let_binding(pat, typ, temp_name, false),
        })
}

pub(crate) fn make_equations<'a>(
    name: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    RcDoc::as_string("Equations")
        .append(RcDoc::space())
        .append(make_definition_inner(
            name.clone(),
            typ,
            name.append(" := ").append(RcDoc::line()).append(expr),
        ))
}

pub(crate) fn make_definition_inner<'a>(
    name: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    name.clone()
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
        .append(RcDoc::line().append(expr.group()))
        .nest(2)
        .append(RcDoc::as_string("."))
}

pub(crate) fn make_definition<'a>(
    name: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    RcDoc::as_string("Definition")
        .append(RcDoc::space())
        .append(make_definition_inner(name, typ, expr))
}

fn code_block_wrap<'a>(
    expr: RcDoc<'a, ()>,
    location_vars: Option<RcDoc<'a, ()>>,
    interface: Option<RcDoc<'a, ()>>,
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
            .append(RcDoc::space())
            .append(match interface {
                Some(a) => a,
                None => RcDoc::as_string("_"),
            })
            .append(RcDoc::space())
            .append(match result_typ {
                Some(a) => a,
                None => RcDoc::as_string("_"),
            }),
    )
}

fn bind_code<'a>(
    expr: RcDoc<'a, ()>,
    early_return_typ: Option<CarrierTyp>,
    typ: Option<BaseTyp>,
    mutable: bool,
    fun_pat: Pattern,
    fun_body: RcDoc<'a, ()>,
    smv_total: ScopeMutableVars,
) -> RcDoc<'a, ()> {
    let local_vars_total = fset_from_scope(smv_total.clone());

    // let early_return_args = match typ {
    //     Some(x) => get_result_or_option(x),
    //     None => None,
    // };

    RcDoc::as_string("bnd")
        .append(if mutable {
            RcDoc::as_string("m")
        } else {
            RcDoc::nil()
        })
        .append(make_paren(
            match early_return_typ.clone() {
                Some(CarrierTyp::Result(_, (c, _))) => {
                    RcDoc::as_string("ChoiceEqualityMonad.result_bind_code ")
                        .append(translate_base_typ(c))
                }
                Some(CarrierTyp::Option(_)) => {
                    RcDoc::as_string("ChoiceEqualityMonad.option_bind_code")
                }
                None => RcDoc::as_string("_"),
            }
            .append(RcDoc::as_string(" , "))
            .append(match typ {
                Some(typ) => translate_base_typ(typ),
                None => RcDoc::as_string("_"),
            })
            .append(RcDoc::as_string(" , "))
            .append(match early_return_typ.clone() {
                // Some(EarlyReturnType::Result((a, _), _)) | Some(EarlyReturnType::Option((a, _))) => {
                //     translate_base_typ(a)
                // }
                _ => RcDoc::as_string("_"),
            })
            .append(RcDoc::as_string(" , "))
            .append(local_vars_total.clone()),
        ))
        .append(RcDoc::space())
        .append(translate_pattern_tick(fun_pat))
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
    RcDoc::as_string(match enum_name.string.as_str() {
        "Ok" => String::from("inl"),
        "Err" => String::from("inr"),
        _ => enum_name.string,
    })
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
                    make_paren(translate_toplevel_ident(name.0))
                },
            )
            .append(if explicit && tyvec.len() != 0 {
                RcDoc::space().append(RcDoc::intersperse(
                    tyvec
                        .into_iter()
                        .map(|(x, _)| make_paren(translate_base_typ(x))),
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
                        .map(|arg| make_paren(translate_base_typ(arg.0.clone()))),
                    RcDoc::space(),
                )),
        ),
        BaseTyp::Named((ident, _span), Some(args)) => make_paren(
            translate_ident(Ident::TopLevel(ident))
                .append(RcDoc::space())
                .append(RcDoc::intersperse(
                    args.iter()
                        .map(|arg| make_paren(translate_base_typ(arg.0.clone()))),
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
    let mut result_typ = match name.clone() {
        Ident::TopLevel(n) => match top_ctx.functions.get(&FnKey::Independent(n.clone())) {
            Some(FnValue::Local(sig)) => Some(sig.ret.0.clone()),
            Some(FnValue::External(_)) => None,
            Some(FnValue::ExternalNotInHacspec(_)) | None => None,
        },
        _ => None,
    };

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
                    // RcDoc::as_string(if inline { "secret_pure" } else { "secret" }),
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
                    (vec![], args),
                ),
                x => (
                    name,
                    vec![],
                    match x {
                        "uint128_from_le_bytes" | "uint128_from_be_bytes" => Some(BaseTyp::UInt128),
                        "uint64_from_le_bytes" | "uint64_from_be_bytes" => Some(BaseTyp::UInt64),
                        "uint32_from_le_bytes" | "uint32_from_be_bytes" => Some(BaseTyp::UInt32),
                        "uint16_from_le_bytes" | "uint16_from_be_bytes" => Some(BaseTyp::UInt16),
                        "uint8_from_le_bytes" | "uint8_from_be_bytes" => Some(BaseTyp::UInt8),
                        "uint128_to_le_bytes" | "uint128_to_be_bytes" => Some(BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: String::from("U128Word"),
                                    kind: TopLevelIdentKind::Type,
                                },
                                DUMMY_SP.into(),
                            ),
                            None,
                        )),
                        "uint64_to_le_bytes" | "uint64_to_be_bytes" => Some(BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: String::from("U64Word"),
                                    kind: TopLevelIdentKind::Type,
                                },
                                DUMMY_SP.into(),
                            ),
                            None,
                        )),
                        "uint32_to_le_bytes" | "uint32_to_be_bytes" => Some(BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: String::from("U32Word"),
                                    kind: TopLevelIdentKind::Type,
                                },
                                DUMMY_SP.into(),
                            ),
                            None,
                        )),
                        "uint16_to_le_bytes" | "uint16_to_be_bytes" => Some(BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: String::from("U16Word"),
                                    kind: TopLevelIdentKind::Type,
                                },
                                DUMMY_SP.into(),
                            ),
                            None,
                        )),
                        "uint8_to_le_bytes" | "uint8_to_be_bytes" => Some(BaseTyp::Named(
                            (
                                TopLevelIdent {
                                    string: String::from("U8Word"),
                                    kind: TopLevelIdentKind::Type,
                                },
                                DUMMY_SP.into(),
                            ),
                            None,
                        )),
                        _ => result_typ,
                    },
                    (vec![], args),
                ),
            }
        }
        Some((prefix, _)) => {
            let (module_name, prefix_info) =
                translate_prefix_for_func_name(prefix.clone(), top_ctx);

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
                            Some(x) => ((x.0).1).0.clone(),
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
                            Some(BaseTyp::Seq(base_ty)),
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
            };

            result_typ = match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
                prefix_info,
            ) {
                (
                    ARRAY_MODULE,
                    "from_slice" | "from_slice_range" | "set_chunk" | "default" | "create"
                    | "update_slice" | "update" | "update_start" | "from_seq" | "new_",
                    _,
                )
                | (
                    SEQ_MODULE,
                    "slice"
                    | "slice_range"
                    | "from_slice"
                    | "concat"
                    | "concat_owned"
                    | "push"
                    | "push_owned"
                    | "from_slice_range"
                    | "get_exact_chunk"
                    | "get_remainder_chunk"
                    | "set_chunk"
                    | "set_exact_chunk"
                    | "create"
                    | "update_slice"
                    | "update"
                    | "update_start"
                    | "from_seq"
                    | "from_public_seq"
                    | "declassify",
                    _,
                )
                | (
                    NAT_MODULE,
                    "zero"
                    | "one"
                    | "two"
                    | "from_secret_literal"
                    | "from_literal"
                    | "pow"
                    | "pow2",
                    _,
                )
                | ("uint128", "declassify", _) => Some(prefix.clone()), // Self
                (ARRAY_MODULE, "length" | "num_chunks" | "get_chunk_len", _)
                | (SEQ_MODULE, "num_chunks" | "num_exact_chunks" | "len", _) => {
                    Some(BaseTyp::Usize)
                }
                (ARRAY_MODULE, "concat" | "slice" | "slice_range", FuncPrefix::Array(_, typ)) => {
                    Some(BaseTyp::Seq(Box::new((typ, DUMMY_SP.into()))))
                }
                (ARRAY_MODULE, "to_be_bytes", _) => {
                    Some(BaseTyp::Seq(Box::new((BaseTyp::UInt8, DUMMY_SP.into()))))
                }

                (ARRAY_MODULE, "get_chunk", FuncPrefix::Array(_, typ))
                | (SEQ_MODULE, "get_chunk", FuncPrefix::Seq(typ)) => Some(BaseTyp::Tuple(vec![
                    (BaseTyp::Usize, DUMMY_SP.into()),
                    (
                        BaseTyp::Seq(Box::new((typ, DUMMY_SP.into()))),
                        DUMMY_SP.into(),
                    ),
                ])),

                (_, _, _) => {
                    println!(
                        "UNCAUGHT: {:?}",
                        module_name
                            .clone()
                            .append(RcDoc::as_string("_"))
                            .append(func_ident.clone())
                    );
                    result_typ
                }
            };

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
        Expression::QuestionMark(_, _) => todo!(),
        Expression::MonadicLet(_, _, _, _) => todo!(),
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
                match op {
                    BinOpKind::Add
                    | BinOpKind::Sub
                    | BinOpKind::Mul
                    | BinOpKind::Div
                    | BinOpKind::Rem => op_typ.clone().map(|(_, (x, _))| x),
                    BinOpKind::And | BinOpKind::Or => Some(BaseTyp::Bool), // = op_typ
                    // BinOpKind::BitXor => Some(BaseTyp::Bool)
                    // BinOpKind::BitAnd => Some(BaseTyp::)
                    // BinOpKind::BitOr => Some(BaseTyp::)
                    // BinOpKind::Shl => Some(BaseTyp::)
                    // BinOpKind::Shr => Some(BaseTyp::)
                    BinOpKind::Lt
                    | BinOpKind::Le
                    | BinOpKind::Ne
                    | BinOpKind::Ge
                    | BinOpKind::Gt
                    | BinOpKind::Eq => Some(BaseTyp::Bool),
                    _ => None,
                },
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
            // ass.extend(ass_e1_0_iter.into_iter().fold(Vec::new(), |mut v, x| {
            //     v.extend(x);
            //     v
            // }));

            let match_expr = make_paren(code_block_wrap(
                RcDoc::as_string("match")
                    .append(RcDoc::space())
                    .append(trans_arg_0)
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("with"))
                    .append(RcDoc::line())
                    .append(RcDoc::intersperse(
                        ass_e1_0_iter
                            .into_iter()
                            .zip(trans_e1_0_iter.into_iter())
                            .map(|(enum_ass, (enum_name, case_name, payload, trans_e1_0))| {
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
                                    .append(RcDoc::concat(enum_ass.into_iter()))
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string("ret"))
                                    .append(RcDoc::space())
                                    .append(make_paren(trans_e1_0))
                            }),
                        RcDoc::line(),
                    ))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("end")),
                None,
                None,
                None,
            ));

            let temp_name = Ident::Local(LocalIdent {
                id: fresh_codegen_id(),
                name: String::from("temp"),
                mutable: false,
            });

            let temp_ass: RcDoc<'a, ()> = make_let_binding(
                Pattern::IdentPat(temp_name.clone(), false),
                None,
                match_expr,
                !inline,
            );
            ass.push(temp_ass);

            (ass, translate_ident(temp_name))
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
                        .append(RcDoc::as_string("then (*inline*)"))
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
                func_ret_ty,
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
                    .append(arg_trans.clone());

                let temp_name = Ident::Local(LocalIdent {
                    id: fresh_codegen_id(),
                    name: String::from("temp"),
                    mutable: false,
                });

                let temp_ass: RcDoc<'a, ()> = make_let_binding(
                    Pattern::IdentPat(temp_name.clone(), false),
                    func_ret_ty,
                    method_call_expr,
                    !inline,
                );
                ass.push(temp_ass);

                (ass, translate_ident(temp_name))
            }
        }
        Expression::ArrayIndex(x, e2, typ) => {
            let e2 = e2.0;
            let array_or_seq = array_or_seq(typ.clone().unwrap(), top_ctx);

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
                match typ.clone() {
                    Some((_, (BaseTyp::Array(_, bt) | BaseTyp::Seq(bt), _))) => Some((*bt).0),
                    _ => None,
                },
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

            let mut ass = ass_iter.into_iter().fold(Vec::new(), |mut v, x| {
                v.extend(x);
                v
            });

            let array_typ = BaseTyp::Array(
                (ArraySize::Integer(trans_iter.len()), DUMMY_SP.into()),
                Box::new((inner_ty.clone(), DUMMY_SP.into())),
            );

            let trans = make_list(trans_iter);
            let cast_trans = match _array_name {
                // Seq case
                None => RcDoc::as_string("seq_from_list _")
                    .append(RcDoc::space())
                    .append(trans),
                Some(_) =>
                // Array case
                {
                    let temp_name = Ident::Local(LocalIdent {
                        id: fresh_codegen_id(),
                        name: String::from("temp"),
                        mutable: false,
                    });
                    let temp_ass: RcDoc<'a, ()> = make_let_binding(
                        Pattern::IdentPat(temp_name.clone(), false),
                        Some(array_typ),
                        RcDoc::as_string(format!("{}_from_list", ARRAY_MODULE))
                            .append(RcDoc::space())
                            .append(make_paren(translate_base_typ(inner_ty.clone())))
                            .append(RcDoc::space())
                            .append(trans),
                        !inline,
                    );
                    ass.push(temp_ass);
                    translate_ident(temp_name)
                }
            };

            (ass, cast_trans)
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
    function_dependencies: FunctionDependencies,
) -> RcDoc<'a, ()> {
    let s = match statements.next() {
        None => return RcDoc::nil(),
        Some(s) => s.clone(),
    };

    match s.0 {
        Statement::LetBinding((pat, _), typ, (expr, _), question_mark) => {
            let (ass_expr, trans_expr) = translate_expression(expr.clone(), top_ctx, inline);
            let trans_stmt = translate_statements(
                statements,
                top_ctx,
                inline,
                smv.clone(),
                function_dependencies.clone(),
            );

            let expr = match question_mark {
                Some((smv_bind, function_dependencies_bind, early_return_typ)) => bind_code(
                    code_block_wrap(
                        RcDoc::concat(ass_expr.into_iter())
                            .append(RcDoc::as_string("@ret _ ").append(make_paren(trans_expr))),
                        Some(make_paren(fset_from_scope(smv_bind.clone()))),
                        Some(function_dependencies_to_interface(
                            function_dependencies_bind.clone(),
                            top_ctx,
                        )), // TODO:?
                        None,
                    ),
                    early_return_typ,              // None,
                    typ.map(|((_, (x, _)), _)| x), // = early_return_typ
                    if let Pattern::IdentPat(_i, true) = pat.clone() {
                        true
                    } else {
                        false
                    },
                    pat.clone(),
                    code_block_wrap(
                        trans_stmt,
                        Some(make_paren(fset_from_scope(smv.clone()))),
                        Some(function_dependencies_to_interface(
                            function_dependencies.clone(),
                            top_ctx,
                        )),
                        None,
                    ),
                    smv.clone(),
                ),
                None => if let Pattern::IdentPat(_i, true) = pat.clone() {
                    // TODO: encapsulate in scope its own varaible
                    make_put_binding(
                        pat.clone(),
                        typ.map(|((_, (base_typ, _)), _)| base_typ),
                        RcDoc::concat(ass_expr.into_iter()).append(
                            RcDoc::as_string("ret")
                                .append(RcDoc::space())
                                .append(make_paren(trans_expr)),
                        ),
                    )
                } else {
                    make_let_binding(
                        pat.clone(),
                        typ.map(|((_, (base_typ, _)), _)| base_typ),
                        RcDoc::concat(ass_expr.into_iter()).append(
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
        Statement::Reassignment((x, _), x_typ, (e1, _), question_mark) => {
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let trans_stmt = translate_statements(
                statements,
                top_ctx,
                inline,
                smv.clone(),
                function_dependencies.clone(),
            );

            let trans_e1 = make_paren(
                RcDoc::concat(ass_e1.into_iter()).append(
                    RcDoc::as_string("ret")
                        .append(RcDoc::space())
                        .append(make_paren(trans_e1)),
                ),
            );

            let expr = match question_mark {
                Some((_smv_bind, function_dependencies_bind, early_return_typ)) => bind_code(
                    code_block_wrap(trans_e1, None, None, None),
                    early_return_typ,
                    x_typ.clone().map(|((_, (base_typ, _)), _)| base_typ),
                    true,
                    Pattern::IdentPat(x.clone(), true),
                    code_block_wrap(
                        trans_stmt,
                        Some(make_paren(fset_from_scope(smv.clone()))),
                        Some(function_dependencies_to_interface(
                            function_dependencies.clone(),
                            top_ctx,
                        )),
                        None,
                    ),
                    smv.clone(),
                ),
                None => make_put_binding(
                    Pattern::IdentPat(x.clone(), true),
                    x_typ.clone().map(|((_, (base_typ, _)), _)| base_typ),
                    trans_e1,
                )
                .append(RcDoc::hardline())
                .append(trans_stmt),
            };

            expr
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.clone().unwrap(), top_ctx);
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2.clone(), top_ctx, inline);

            let trans_stmt = translate_statements(
                statements,
                top_ctx,
                inline,
                smv.clone(),
                function_dependencies.clone(),
            );

            let expr = match question_mark {
                Some((_smv_bind, function_dependencies_bind, early_return_typ)) => bind_code(
                    trans_e2,
                    early_return_typ,
                    typ.clone().map(|(_, (x, _))| x),
                    false, // TODO: is this never mutable?
                    Pattern::IdentPat(
                        Ident::Local(LocalIdent {
                            id: 0,
                            name: String::from("_temp"),
                            mutable: false,
                        }),
                        false,
                    ),
                    make_let_binding(
                        Pattern::IdentPat(x.clone(), false),
                        typ.clone().map(|(_, (base_typ, _))| base_typ),
                        (RcDoc::concat(ass_e1.into_iter()))
                            .append(RcDoc::concat(ass_e2.into_iter()))
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
                        typ.clone().map(|(_, (x, _))| x),
                        (RcDoc::concat(ass_e1.into_iter()))
                            .append(RcDoc::concat(ass_e2.into_iter()))
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

            RcDoc::concat(ass_e1.into_iter())
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
            let mut block_1 = translate_block(b1.clone(), true, top_ctx, inline, false);
            if !b1_question_mark {
                let local_vars_b1 = fset_from_scope(b1.mutable_vars.clone());
                let interface_b1 =
                    function_dependencies_to_interface(b1.function_dependencies.clone(), top_ctx);
                block_1 = RcDoc::as_string("let temp_then := ")
                    .append(block_1)
                    .append(RcDoc::as_string(" in"))
                    .append(RcDoc::line())
                    .append(code_block_wrap(
                        RcDoc::as_string("temp_then"),
                        Some(make_paren(local_vars_b1)),
                        Some(interface_b1),
                        None,
                    ));
            }

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
                    )]
                    .iter(),
                    top_ctx,
                    inline,
                    smv.clone(),
                    function_dependencies.clone(),
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

                    let block2_expr = translate_block(b2, true, top_ctx, inline, true);

                    RcDoc::space().append(make_paren(block2_expr))
                }
            };

            let trans_stmt = translate_statements(
                statements.clone(),
                top_ctx,
                inline,
                smv.clone(),
                function_dependencies.clone(),
            );

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
                .append(RcDoc::as_string("then (*state*)"))
                .append(RcDoc::space())
                .append(make_paren(code_block_wrap(
                    block_1.clone(),
                    Some(make_paren(fset_from_scope(b1.mutable_vars.clone()))),
                    Some(function_dependencies_to_interface(
                        b1.function_dependencies,
                        top_ctx,
                    )),
                    None,
                )))
                .append(RcDoc::line())
                .append(RcDoc::as_string("else"))
                .append(RcDoc::space())
                .append(code_block_wrap(
                    else_expr,
                    b2.clone()
                        .map(|(b2, _)| make_paren(fset_from_scope(b2.mutable_vars.clone()))),
                    b2.clone().map(|(b2, _)| {
                        function_dependencies_to_interface(b2.function_dependencies, top_ctx)
                    }),
                    None,
                ))
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
                    match mutated_info.stmt {
                        Statement::ReturnExp(e, t) => t.clone().map(|(_, (base_typ, _))| base_typ),
                        _ => None,
                    },
                    false, // TODO: this should be mutable? or not?
                    pat,
                    code_block_wrap(
                        trans_stmt,
                        Some(make_paren(fset_from_scope(smv.clone()))),
                        Some(function_dependencies_to_interface(
                            function_dependencies,
                            top_ctx,
                        )),
                        None,
                    ),
                    smv.clone(),
                )
            } else {
                let expr = RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(trans_cond.clone())
                    .append(RcDoc::as_string(":bool_ChoiceEquality"))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("then (*not state*)"))
                    .append(RcDoc::space())
                    .append(make_paren(block_1.clone()))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("else"))
                    .append(RcDoc::space())
                    .append(else_expr);

                make_let_binding(
                    pat,
                    match mutated_info.stmt {
                        Statement::ReturnExp(e, t) => t.clone().map(|(_, (base_typ, _))| base_typ),
                        _ => None,
                    },
                    // b1.return_typ.map(|(_, (base_typ, _))| base_typ),
                    // None,
                    expr,
                    !inline,
                )
                .append(RcDoc::hardline())
                .append(trans_stmt)
            };

            RcDoc::concat(ass_cond.into_iter()).append(either_expr)
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

            let block_expr = translate_block(b.clone(), true, top_ctx, inline, true);
            let trans_stmt = translate_statements(
                statements,
                top_ctx,
                inline,
                smv.clone(),
                function_dependencies.clone(),
            );

            let expr = if b_question_mark {
                let local_vars_bind = fset_from_scope(b.mutable_vars.clone());
                let local_vars_fun = fset_from_scope(smv.clone());

                let loop_expr = RcDoc::as_string("foldi_bind_code'")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .append(RcDoc::space())
                    .append(make_paren(
                        // RcDoc::as_string("lift_to_code (ChoiceEqualityMonad.ret ")
                        // .append(
                        match mut_tuple.clone() {
                            Pattern::Tuple(_) => RcDoc::as_string("prod_ce")
                                .append(translate_pattern(mut_tuple.clone())),
                            _ => translate_pattern(mut_tuple.clone()),
                        }, // )
                           // .append(RcDoc::as_string(")")), // TODO: Ok only when result
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
                    match mutated_info.stmt {
                        Statement::ReturnExp(e, t) => t.clone().map(|(_, (base_typ, _))| base_typ),
                        _ => None,
                    },
                    false,             // TODO: should this be mutable?
                    mut_tuple.clone(), // TODO: Issue here with patterns (eg. 'tt)
                    code_block_wrap(
                        trans_stmt,
                        Some(make_paren(fset_from_scope(b.mutable_vars.clone()))),
                        Some(function_dependencies_to_interface(
                            b.function_dependencies,
                            top_ctx,
                        )),
                        None,
                    ),
                    smv.clone(),
                )
            } else {
                let loop_expr = RcDoc::as_string("foldi'")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .append(RcDoc::space())
                    .append(match mut_tuple.clone() {
                        Pattern::Tuple(_) => {
                            RcDoc::as_string("prod_ce").append(translate_pattern(mut_tuple.clone()))
                        }
                        _ => translate_pattern(mut_tuple.clone()),
                    })
                    .append(RcDoc::space())
                    .append(make_paren(
                        RcDoc::as_string("L2 := ").append(fset_from_scope(smv.clone())),
                    ))
                    .append(RcDoc::space())
                    .append(make_paren(RcDoc::as_string("I2 := ").append(
                        function_dependencies_to_interface(function_dependencies, top_ctx),
                    )))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(H_loc_incl := _) (H_opsig_incl := _)"))
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
                    .append(RcDoc::as_string(")"))
                    .group()
                    .nest(2);

                make_let_binding(
                    mut_tuple.clone(),
                    match mutated_info.stmt {
                        Statement::ReturnExp(e, t) => t.clone().map(|(_, (base_typ, _))| base_typ),
                        _ => None,
                    },
                    loop_expr,
                    !inline,
                )
                .append(RcDoc::hardline())
                .append(trans_stmt)
            };

            RcDoc::concat(ass_e1.into_iter())
                .append(RcDoc::concat(ass_e2.into_iter()))
                .append(expr)
        }
    }
    // .group()
}

fn list_of_loc_vars<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    // let mut all = smvars.external_vars.clone();
    // all.extend(locals.clone());

    RcDoc::as_string("[")
        .append(RcDoc::intersperse(
            locals // alls
                .into_iter()
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

pub fn function_dependencies_to_vec<'a>(
    function_dependencies: FunctionDependencies,
    top_ctx: &'a TopLevelContext,
) -> Vec<(TopLevelIdent, Vec<BaseTyp>, BaseTyp)> {
    let mut dep_info = vec![];
    for x in function_dependencies.0 {
        match top_ctx.functions.get(&FnKey::Independent(x.clone())) {
            Some(FnValue::Local(fnsig)) => {
                let mut unspanned_args = vec![];
                for ((_a, _), ((_, (bt, _)), _)) in fnsig.args.clone() {
                    unspanned_args.push(bt)
                }
                dep_info.push((x, unspanned_args, fnsig.ret.0.clone()))
            }
            Some(FnValue::External(fnsig)) => {
                match x.string.as_str() {
                    // hacspec library functions
                    "ZERO"
                    | "ONE"
                    | "TWO"
                    | "from_literal"
                    | "from_hex_string"
                    | "get_bit"
                    | "set_bit"
                    | "set"
                    | "rotate_left"
                    | "rotate_right"
                    | "max_val"
                    | "wrap_add"
                    | "wrap_sub"
                    | "wrap_mul"
                    | "wrap_div"
                    | "exp"
                    | "pow_self"
                    | "divide"
                    | "inv"
                    | "equal"
                    | "greater_than"
                    | "greater_than_or_qual"
                    | "less_than"
                    | "less_than_or_equal"
                    | "not_equal_bm"
                    | "equal_bm"
                    | "greater_than_bm"
                    | "greater_than_or_equal_bm"
                    | "less_than_bm"
                    | "less_than_or_equal_bm"
                    | "sub_mod"
                    | "add_mod"
                    | "mul_mod"
                    | "pow_mod"
                    | "modulo"
                    | "signed_modulo"
                    | "absolute"
                    | "classify"
                    | "to_le_bytes"
                    | "to_be_bytes"
                    | "from_le_bytes"
                    | "from_be_bytes"
                    | "extended_euclid_internal"
                    | "cswap_bit"
                    | "cswap"
                    | "cset_bit"
                    | "cadd"
                    | "csub"
                    | "cmul"
                    | "ct_div"
                    | "poly_sub"
                    | "poly_add"
                    | "poly_mul"
                    | "scalar_div"
                    | "mul_poly_naive"
                    | "invert_fermat"
                    | "sub_poly"
                    | "add_poly"
                    | "div_scalar"
                    | "degree_poly"
                    | "extended_euclid"
                    | "extended_euclid_invert"
                    | "poly_to_ring"
                    | "mul_poly_irr"
                    | "new"
                    | "length"
                    | "from_array"
                    | "from_native_slice"
                    | "from_slice"
                    | "concat"
                    | "from_slice_range"
                    | "slice"
                    | "slice_range"
                    | "num_chunks"
                    | "get_chunk_len"
                    | "get_chunk"
                    | "set_chunk"
                    | "default"
                    | "create"
                    | "len"
                    | "iter"
                    | "update_slice"
                    | "update"
                    | "update_start"
                    | "index"
                    | "index_mut"
                    | "from_vec"
                    | "from_seq"
                    | "from_hex"
                    | "fmt"
                    | "declassify_eq"
                    | "from_public_slice"
                    | "from_public_array"
                    | "add"
                    | "sub"
                    | "mul"
                    | "rem"
                    | "not"
                    | "bitor"
                    | "bitxor"
                    | "bitand"
                    | "shr"
                    | "shl"
                    | "to_be_U32s"
                    | "to_le_U32s"
                    | "to_be_U64s"
                    | "to_le_U64s"
                    | "to_U128s_be"
                    | "to_U128s_le"
                    | "to_hex"
                    | "into_le_bytes"
                    | "eq"
                    | "partial_cmp"
                    | "cmp"
                    | "with_capacity"
                    | "reserve"
                    | "native_slice"
                    | "into_slice"
                    | "into_slice_range"
                    | "split_off"
                    | "truncate"
                    | "concat_owned"
                    | "push"
                    | "push_owned"
                    | "num_exact_chunks"
                    | "get_exact_chunk"
                    | "get_remainder_chunk"
                    | "set_exact_chunk"
                    | "from_string"
                    | "from_public_seq"
                    | "declassify"
                    | "into_native"
                    | "to_native"
                    | "get_byte"
                    | "U16_to_le_bytes"
                    | "U16_to_be_bytes"
                    | "U16_from_be_bytes"
                    | "U16_from_le_bytes"
                    | "U32_to_le_bytes"
                    | "U32_to_be_bytes"
                    | "U32_from_be_bytes"
                    | "U32_from_le_bytes"
                    | "U64_to_le_bytes"
                    | "U64_to_be_bytes"
                    | "U64_from_be_bytes"
                    | "U64_from_le_bytes"
                    | "U128_to_le_bytes"
                    | "U128_to_be_bytes"
                    | "U128_from_be_bytes"
                    | "U128_from_le_bytes"
                    | "u16_to_le_bytes"
                    | "u16_to_be_bytes"
                    | "u16_from_be_bytes"
                    | "u16_from_le_bytes"
                    | "u32_to_le_bytes"
                    | "u32_to_be_bytes"
                    | "u32_from_be_bytes"
                    | "u32_from_le_bytes"
                    | "u64_to_le_bytes"
                    | "u64_to_be_bytes"
                    | "u64_from_be_bytes"
                    | "u64_from_le_bytes"
                    | "u128_to_le_bytes"
                    | "u128_to_be_bytes"
                    | "u128_from_be_bytes"
                    | "u128_from_le_bytes"
                    | "hex_string_to_bytes"
                    | "to_array"
                    | "vec_poly_mul"
                    | "vec_poly_add"
                    | "vec_poly_sub"
                    | "pad"
                    | "make_fixed_length"
                    | "monomial"
                    | "normalize"
                    | "leading_coefficient"
                    | "is_zero"
                    | "from_byte_seq_be"
                    | "from_public_byte_seq_be"
                    | "to_byte_seq_be"
                    | "from_public"
                    | "from_secret_declassify"
                    | "to_public_byte_seq_be"
                    | "from_byte_seq_le"
                    | "from_public_byte_seq_le"
                    | "to_byte_seq_le"
                    | "to_public_byte_seq_le"
                    | "from_secret_literal" => (),
                    // Uncaught hacspec library functions?
                    "U8"
                    | "U16"
                    | "U32"
                    | "U64"
                    | "U128"
                    | "clone"
                    | "U8_from_usize"
                    | "declassify_usize_from_U8" => (),
                    _ => {
                        println!("External not caught {:?}", x.string);
                        let mut unspanned_args = vec![];
                        for ((_a, _), (bt, _)) in fnsig.args.clone() {
                            unspanned_args.push(bt)
                        }
                        dep_info.push((x, unspanned_args, fnsig.ret.clone()))
                        // dep_info.push(format!("{:?}", x.clone())),
                    }
                }
            }
            Some(_) => (),
            None => (), // println!("Fn {} is non", x.clone()),
        }
    }
    dep_info.sort_by(|(a, _, _), (b, _, _)| a.partial_cmp(b).unwrap());
    dep_info
}

pub(crate) fn function_dependencies_to_interface<'a>(
    function_dependencies: FunctionDependencies,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    let dep_info = function_dependencies_to_vec(function_dependencies, top_ctx);

    RcDoc::as_string("[interface")
        .append(if dep_info.clone().is_empty() {
            RcDoc::nil()
        } else {
            RcDoc::softline()
                .append(RcDoc::intersperse(
                    dep_info.clone().into_iter().map(|(x, _v, _r)| {
                        RcDoc::as_string("#val #[ ")
                            .append(RcDoc::as_string(x.clone().string.to_uppercase()))
                            .append(RcDoc::as_string(" ] : "))
                            .append(translate_ident(Ident::TopLevel(x.clone())).append("_inp"))
                            .append(
                                RcDoc::as_string(" → ").append(
                                    translate_ident(Ident::TopLevel(x.clone())).append("_out"),
                                ),
                            )
                    }),
                    RcDoc::space()
                        .append(RcDoc::as_string(";"))
                        .append(RcDoc::softline()),
                ))
                .append(RcDoc::softline())
        })
        .append("]")
}

pub(crate) fn function_dependencies_to_imports<'a>(
    function_dependencies: FunctionDependencies,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    let dep_info = function_dependencies_to_vec(function_dependencies, top_ctx);

    RcDoc::intersperse(
        dep_info.clone().into_iter().map(|(x, v, _r)| {
            RcDoc::as_string("#import {sig #[ ")
                .append(RcDoc::as_string(x.clone().string.to_uppercase()))
                .append(RcDoc::as_string(" ] : "))
                .append(translate_ident(Ident::TopLevel(x.clone())).append("_inp"))
                .append(RcDoc::as_string(" → "))
                .append(translate_ident(Ident::TopLevel(x.clone())).append("_out"))
                .append(RcDoc::space())
                .append(RcDoc::as_string("} as"))
                .append(RcDoc::space())
                .append(translate_ident(Ident::TopLevel(x.clone())))
                .append(RcDoc::space())
                .append(RcDoc::as_string(";;"))
                .append(RcDoc::line())
                .append(RcDoc::as_string("let "))
                .append(translate_ident(Ident::TopLevel(x.clone())))
                .append(RcDoc::as_string(" := "))
                .append(if v.len() > 0 {
                    RcDoc::as_string("fun ")
                        .append(RcDoc::intersperse(
                            (0..v.len())
                                .into_iter()
                                .map(|x| RcDoc::as_string(format!("x_{}", x))),
                            RcDoc::space(),
                        ))
                        .append(RcDoc::as_string(" => "))
                } else {
                    RcDoc::nil()
                })
                .append(translate_ident(Ident::TopLevel(x.clone())))
                .append(RcDoc::space())
                .append(if v.len() > 0 {
                    make_paren(RcDoc::intersperse(
                        (0..v.len())
                            .into_iter()
                            .map(|x| RcDoc::as_string(format!("x_{}", x))),
                        RcDoc::as_string(","),
                    ))
                } else {
                    RcDoc::as_string("tt")
                })
                .append(RcDoc::as_string(" in"))
                .append(RcDoc::line())
        }),
        RcDoc::nil(),
    )
}

fn translate_block<'a>(
    b: Block,
    omit_extra_unit: bool,
    top_ctx: &'a TopLevelContext,
    inline: bool,
    wrap: bool,
) -> RcDoc<'a, ()> {
    let mut statements = b.stmts;
    match (&b.return_typ, omit_extra_unit) {
        (None, _) => panic!(), // should not happen,
        (Some(((Borrowing::Consumed, _), (BaseTyp::Tuple(args), _))), false) if args.is_empty() => {
            statements.push((
                Statement::ReturnExp(Expression::Lit(Literal::Unit), b.return_typ),
                DUMMY_SP.into(),
            ));
        }
        (Some(_), _) => (),
    }

    let trans_stmt = translate_statements(
        statements.iter(),
        top_ctx,
        inline,
        b.mutable_vars.clone(),
        b.function_dependencies.clone(),
    );
    let local_vars = fset_from_scope(b.mutable_vars);
    let interface = function_dependencies_to_interface(b.function_dependencies.clone(), top_ctx);

    if wrap {
        code_block_wrap(
            trans_stmt.group(),
            Some(make_paren(local_vars)),
            Some(interface),
            None,
        )
    } else {
        trans_stmt.group()
    }
}

pub(crate) fn translate_item<'a>(
    item: DecoratedItem,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    match &item.item {
        Item::FnDecl((f, _), sig, (b, _)) => {
            let interface =
                function_dependencies_to_interface(sig.function_dependencies.clone(), top_ctx);
            let fun_imports =
                function_dependencies_to_imports(sig.function_dependencies.clone(), top_ctx);

            let block_exprs = translate_block(b.clone(), false, top_ctx, false, true);
            let (block_vars, block_var_loc_defs) = fset_and_locations(sig.mutable_vars.clone());

            let inp_typ = if sig.args.is_empty() {
                translate_base_typ(UnitTyp)
            } else {
                RcDoc::intersperse(
                    sig.args
                        .iter()
                        .map(|((_x, _), (tau, _))| translate_typ(tau.clone())),
                    RcDoc::space()
                        .append(RcDoc::as_string("'×"))
                        .append(RcDoc::space()),
                )
            };

            let fun_inp_notation = RcDoc::as_string("Notation")
                .append(RcDoc::space())
                .append(RcDoc::as_string("\"'"))
                .append(
                    translate_ident(Ident::TopLevel(f.clone())).append(RcDoc::as_string("_inp")),
                )
                .append(RcDoc::as_string("'\""))
                .append(RcDoc::space())
                .append(RcDoc::as_string(":="))
                .append(RcDoc::space())
                .append(make_paren(
                    inp_typ.clone().append(RcDoc::as_string(" : choice_type")),
                ))
                .append(RcDoc::as_string(" (in custom pack_type at level 2)."));

            let fun_out_notation = RcDoc::as_string("Notation")
                .append(RcDoc::space())
                .append(RcDoc::as_string("\"'"))
                .append(
                    translate_ident(Ident::TopLevel(f.clone())).append(RcDoc::as_string("_out")),
                )
                .append(RcDoc::as_string("'\""))
                .append(RcDoc::space())
                .append(RcDoc::as_string(":="))
                .append(RcDoc::space())
                .append(make_paren(
                    translate_base_typ(sig.ret.0.clone())
                        .append(RcDoc::as_string(" : choice_type")),
                ))
                .append(RcDoc::as_string(" (in custom pack_type at level 2)."));

            let fun_ident_def = make_definition(
                RcDoc::as_string(f.clone().string.to_uppercase()),
                Some(RcDoc::as_string("nat")),
                RcDoc::as_string(fresh_codegen_id()),
            );

            let fun_def_sig = translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::line())
                            // .append(if sig.args.len() > 0 {
                            //     RcDoc::intersperse(
                            //         sig.args.iter().map(|((x, _), (tau, _))| {
                            //             make_paren(
                            //                 translate_ident(x.clone())
                            //                     .append(RcDoc::space())
                            //                     .append(RcDoc::as_string(":"))
                            //                     .append(RcDoc::space())
                            //                     .append(translate_typ(tau.clone())),
                            //             )
                            //         }),
                            //         RcDoc::line(),
                            //     )
                            // } else {
                            //     RcDoc::nil()
                            // })
                ;

            let fun_type = RcDoc::as_string("package")
                .append(RcDoc::space())
                .append(make_paren(block_vars))
                .append(RcDoc::space())
                .append(interface)
                .append(RcDoc::space())
                .append(
                    RcDoc::as_string("[interface")
                        .append(RcDoc::softline())
                        .append(RcDoc::as_string("#val #[ "))
                        .append(RcDoc::as_string(f.clone().string.to_uppercase()))
                        .append(RcDoc::as_string(" ] : "))
                        .append(translate_ident(Ident::TopLevel(f.clone())).append("_inp"))
                        .append(
                            RcDoc::as_string(" → ")
                                .append(translate_ident(Ident::TopLevel(f.clone())).append("_out")),
                        )
                        .append(RcDoc::softline())
                        .append("]"),
                );

            let package_wraped_code_block = RcDoc::as_string("[package #def #[ ")
                .append(RcDoc::as_string(f.clone().string.to_uppercase()))
                .append(RcDoc::as_string(" ] (temp_inp : "))
                .append(translate_ident(Ident::TopLevel(f.clone())).append("_inp"))
                .append(RcDoc::as_string(") : "))
                .append(translate_ident(Ident::TopLevel(f.clone())).append("_out"))
                .append(RcDoc::as_string(" { "))
                .append(RcDoc::line())
                .append(if !sig.args.is_empty() {
                    RcDoc::as_string("let '")
                        .append(make_paren(RcDoc::intersperse(
                            sig.args
                                .iter()
                                .map(|((x, _), (_tau, _))| translate_ident(x.clone())),
                            RcDoc::space()
                                .append(RcDoc::as_string(","))
                                .append(RcDoc::space()),
                        )))
                        .append(RcDoc::as_string(" := temp_inp : "))
                        .append(inp_typ)
                        .append(RcDoc::as_string(" in"))
                        .append(RcDoc::line())
                } else {
                    RcDoc::nil()
                })
                .append(fun_imports)
                .append(block_exprs.group())
                .append(RcDoc::line())
                .append(RcDoc::as_string("}]"));

            let dep_vec = function_dependencies_to_vec(sig.function_dependencies.clone(), top_ctx);
            let package_def =
                make_equations(
                        RcDoc::as_string("package_")
                            .append(translate_ident(Ident::TopLevel(f.clone()))),
                        Some(RcDoc::as_string("package _ _ _")),
                        if dep_vec.is_empty() {
                            translate_ident(Ident::TopLevel(f.clone()))
                        } else {
                            RcDoc::as_string("seq_link")
                                .append(RcDoc::space())
                                .append(translate_ident(Ident::TopLevel(f.clone())))
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("link_rest"))
                                .append(make_paren(RcDoc::intersperse(
                                    dep_vec.into_iter().map(|(x, _, _)| {
                                        RcDoc::as_string("package_")
                                            .append(translate_toplevel_ident(x))
                                    }),
                                    RcDoc::as_string(","),
                                )))
                        },
                    );

            block_var_loc_defs
                .append(RcDoc::line())
                .append(fun_inp_notation)
                .append(RcDoc::line())
                .append(fun_out_notation)
                .append(RcDoc::line())
                .append(fun_ident_def)
                .append(RcDoc::line())
                .append(make_equations(
                    fun_def_sig,
                    Some(fun_type),
                    package_wraped_code_block,
                ))
                .append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))
                .append(RcDoc::hardline())
                .append(package_def)
                .append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))
        }
        Item::EnumDecl(name, cases) => make_definition(
            translate_enum_name(name.0.clone()),
            Some(RcDoc::as_string("ChoiceEquality")),
            RcDoc::intersperse(
                cases.into_iter().map(|(case_name, case_typ)| {
                    translate_base_typ(match case_typ {
                        None => UnitTyp,
                        Some((bty, _)) => bty.clone(),
                    })
                }),
                RcDoc::space()
                    .append(RcDoc::as_string("'+"))
                    .append(RcDoc::space()),
            ),
        )
        .append(RcDoc::line())
        .append(RcDoc::intersperse(
            cases
                .into_iter()
                .enumerate()
                .map(|(i, (case_name, case_typ))| {
                    let name_ty = BaseTyp::Named(name.clone(), None);

                    let index = if cases.len() == 1 {
                        String::from("")
                    } else {
                        "0".repeat(cases.len() - 1 - i) + if i == 0 { "" } else { "1" }
                    };
                    // format!("{:#b}", cases.len()-1-i).replace("0b","")
                    // .map(|c| {
                    //     match c {
                    //         '0' => "inl",
                    //         '1' => "inr",
                    //         _ => panic!("Should be binary")
                    //     }
                    // })
                    make_definition(
                        translate_enum_case_name(name_ty.clone(), case_name.0.clone(), false)
                            .append(match case_typ {
                                Some((bty, _)) => RcDoc::space().append(make_paren(
                                    RcDoc::as_string("x : ")
                                        .append(translate_base_typ(bty.clone())),
                                )),
                                None => RcDoc::nil(),
                            }),
                        Some(translate_base_typ(name_ty)),
                        RcDoc::intersperse(
                            index.clone().chars().map(|c| match c {
                                '0' => "inl",
                                '1' => "inr",
                                _ => panic!("Should be binary"),
                            }),
                            RcDoc::as_string(" ("),
                        )
                        .append(match case_typ {
                            Some((bty, _)) => RcDoc::space().append(RcDoc::as_string("x")),
                            None => RcDoc::space().append(RcDoc::as_string("tt")),
                        })
                        .append(RcDoc::intersperse(
                            index.chars().map(|_| RcDoc::nil()),
                            RcDoc::as_string(")"),
                        )),
                    )
                }),
            RcDoc::line(),
        )),
        // .append(if item.tags.0.contains(&"PartialEq".to_string()) {
        //     RcDoc::hardline()
        //         .append(RcDoc::hardline())
        //         .append(make_definition(
        //             RcDoc::as_string("eqb_")
        //                 .append(translate_enum_name(name.0.clone()))
        //                 .append(RcDoc::space())
        //                 .append(RcDoc::as_string("(x y : "))
        //                 .append(translate_enum_name(name.0.clone()))
        //                 .append(RcDoc::as_string(")")),
        //             Some(RcDoc::as_string("bool_ChoiceEquality")),
        //             RcDoc::as_string("match x with")
        //                 .append(RcDoc::line())
        //                 .append(RcDoc::intersperse(
        //                     cases.into_iter().map(|(case_name, case_typ)| {
        //                         let name_ty = BaseTyp::Named(name.clone(), None);
        //                         RcDoc::as_string("|")
        //                             .append(RcDoc::space())
        //                             .append(translate_enum_case_name(
        //                                 name_ty.clone(),
        //                                 case_name.0.clone(), false,
        //                             ))
        //                             .append(RcDoc::space())
        //                             .append(match case_typ {
        //                                 None => RcDoc::nil(),
        //                                 Some(_) => RcDoc::as_string("a").append(RcDoc::space()),
        //                             })
        //                             .append(RcDoc::as_string("=>"))
        //                             .append(RcDoc::line())
        //                             .append(
        //                                 RcDoc::as_string("match y with")
        //                                     .append(RcDoc::line())
        //                                     .append(RcDoc::as_string("|"))
        //                                     .append(RcDoc::space())
        //                                     .append(translate_enum_case_name(
        //                                         name_ty.clone(),
        //                                         case_name.0.clone(), false,
        //                                     ))
        //                                     .append(match case_typ {
        //                                         None => RcDoc::as_string("=> true"),
        //                                         Some(_) => RcDoc::space()
        //                                             .append(RcDoc::as_string("b"))
        //                                             .append(RcDoc::space())
        //                                             .append(RcDoc::as_string("=> a =.? b")),
        //                                     })
        //                                     .append(RcDoc::line())
        //                                     .append(match &cases.into_iter().size_hint().1 {
        //                                         Some(0) => RcDoc::nil(),
        //                                         Some(1) => RcDoc::nil(),
        //                                         _ => RcDoc::as_string("| _ => false")
        //                                             .append(RcDoc::line()),
        //                                     })
        //                                     .append(RcDoc::as_string("end")),
        //                             )
        //                             .group()
        //                             .nest(4)
        //                     }),
        //                     RcDoc::line(),
        //                 ))
        //                 .append(RcDoc::line())
        //                 .append("end.")
        //                 .nest(3)
        //         ))
        //         .append(RcDoc::hardline())
        //         .append(RcDoc::hardline())
        //         .append(RcDoc::as_string("Definition"))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("eqb_leibniz_"))
        //         .append(translate_enum_name(name.0.clone()))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("(x y : "))
        //         .append(translate_enum_name(name.0.clone()))
        //         .append(RcDoc::as_string(") :"))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("eqb_"))
        //         .append(translate_enum_name(name.0.clone()))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("x y = true <-> x = y."))
        //         .append(RcDoc::hardline())
        //         .append(
        //             RcDoc::as_string("Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.")
        //         )
        //         .append(RcDoc::hardline())
        //         .append(RcDoc::hardline())
        //         .append(RcDoc::as_string("Instance"))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("eq_dec_"))
        //         .append(translate_enum_name(name.0.clone()))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string(":"))
        //         .append(RcDoc::space())
        //         .append(RcDoc::as_string("EqDec ("))
        //         .append(translate_enum_name(name.0.clone()))
        //         .append(RcDoc::as_string(") :="))
        //         .append(RcDoc::hardline())
        //         .append(
        //             RcDoc::as_string("Build_EqDec (")
        //                 .append(translate_enum_name(name.0.clone()))
        //                 .append(RcDoc::as_string(") (eqb_"))
        //                 .append(translate_enum_name(name.0.clone()))
        //                 .append(RcDoc::as_string(") (eqb_leibniz_"))
        //                 .append(translate_enum_name(name.0.clone()))
        //                 .append(RcDoc::as_string(")."))
        //                 .nest(2)
        //         )
        //         .append(RcDoc::hardline())
        // } else {
        //     RcDoc::nil()
        // })
        Item::ArrayDecl(name, size, cell_t, index_typ) => {
            let (ass_size_0, trans_size_0) = translate_expression(size.0.clone(), top_ctx, false);
            make_definition(
                translate_ident(Ident::TopLevel(name.0.clone())),
                None,
                RcDoc::concat(ass_size_0.into_iter()).append(
                    RcDoc::line()
                        .append(RcDoc::as_string("nseq"))
                        .append(RcDoc::space())
                        .append(make_paren(translate_base_typ(cell_t.0.clone())))
                        .append(RcDoc::space())
                        .append(make_paren(trans_size_0.clone()))
                        .group()
                        .nest(2),
                ),
            )
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
            make_definition(
                translate_ident(Ident::TopLevel(name.0.clone())),
                Some(make_paren(translate_base_typ(ty.0.clone()))),
                RcDoc::concat(ass_e_0.into_iter()).append(make_paren(trans_e_0)),
            )
        }
        Item::NaturalIntegerDecl(nat_name, _secrecy, canvas_size, info) => {
            let canvas_size = match &canvas_size.0 {
                Expression::Lit(Literal::Usize(size)) => size,
                _ => panic!(), // should not happen by virtue of typchecking
            };
            let canvas_size_bytes = RcDoc::as_string(format!("{}", (canvas_size + 7) / 8));
            (match info {
                Some((canvas_name, _modulo)) => make_definition(
                    translate_ident(Ident::TopLevel(canvas_name.0.clone())),
                    None,
                    RcDoc::as_string("nseq")
                        .append(RcDoc::space())
                        .append(make_paren(translate_base_typ(BaseTyp::UInt8)))
                        .append(RcDoc::space())
                        .append(make_paren(canvas_size_bytes.clone())),
                )
                .append(RcDoc::hardline()),
                None => RcDoc::nil(),
            })
            .append(make_definition(
                translate_ident(Ident::TopLevel(nat_name.0.clone())),
                None,
                RcDoc::as_string("nat_mod")
                    .append(RcDoc::space())
                    .append(match info {
                        Some((_, modulo)) => RcDoc::as_string(format!("0x{}", &modulo.0)),
                        None => RcDoc::as_string(format!("pow2 {}", canvas_size)),
                    }),
            ))
        }
        Item::ImportedCrate((TopLevelIdent { string: kr, .. }, _)) => RcDoc::as_string(format!(
            "Require Import {}.",
            str::replace(&kr.to_title_case(), " ", "_"),
        )),
        // Aliases are translated to Coq Notations
        Item::AliasDecl((ident, _), (ty, _)) => RcDoc::as_string("Notation")
            .append(RcDoc::space())
            .append(RcDoc::as_string("\"'"))
            .append(translate_ident(Ident::TopLevel(ident.clone())))
            .append(RcDoc::as_string("'\""))
            .append(RcDoc::space())
            .append(RcDoc::as_string(":= ("))
            .append(translate_base_typ(ty.clone()))
            .append(RcDoc::as_string(") : hacspec_scope.")),
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
