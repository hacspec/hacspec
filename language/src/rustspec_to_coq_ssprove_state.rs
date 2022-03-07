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

fn make_get_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    typ_after: bool,
) -> RcDoc<'a, ()> {
    pat.clone()
        .append(RcDoc::space())
        .append(RcDoc::as_string("←"))
        .append(RcDoc::space())
        .append(RcDoc::as_string("get"))
        .append(RcDoc::space())
        .append(pat.clone().append(RcDoc::as_string("_loc")).group())
        .append(RcDoc::space())
        .append(RcDoc::as_string(";;"))
        .append(RcDoc::line())
        .append(if let Some(_) = typ.clone() {
            make_let_binding(
                pat.clone(),
                typ.clone(),
                typ_after.clone(),
                pat.clone(),
                false,
                false,
            )
        } else {
            RcDoc::nil()
        })
}

fn make_put_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    typ_after: bool,
    expr: RcDoc<'a, ()>,
) -> RcDoc<'a, ()> {
    RcDoc::as_string("#put")
        .append(RcDoc::space())
        .append(pat.clone().append(RcDoc::as_string("_loc")).group())
        .append(RcDoc::space())
        .append(RcDoc::as_string(":= "))
        .group()
        .append(RcDoc::line().append(make_paren(expr.group())))
        .nest(2)
        .append(RcDoc::space())
        .append(RcDoc::as_string(";;"))
        .append(RcDoc::line())
        .append(make_get_binding(pat, typ, typ_after))
}

fn make_let_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    typ_after: bool,
    expr: RcDoc<'a, ()>,
    toplevel: bool,
    do_bind: bool,
) -> RcDoc<'a, ()> {
    RcDoc::as_string(if toplevel {
        "Definition"
    } else {
        if do_bind {
            ""
        } else {
            "let"
        }
    })
    .append(RcDoc::space())
    .append(
        pat.clone()
            .append(if typ_after || do_bind {
                RcDoc::nil()
            } else {
                match typ.clone() {
                    None => RcDoc::nil(),
                    Some(tau) => RcDoc::space()
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(tau),
                }
            })
            .group(),
    )
    .append(RcDoc::space())
    .append(if do_bind {
        RcDoc::as_string("←")
    } else {
        RcDoc::as_string(":=")
    })
    .group()
    .append(RcDoc::line().append(make_paren(
        expr.group(), // .append(if do_bind {
                      //     match typ.clone() {
                      //         None => RcDoc::nil(),
                      //         Some(tau) => RcDoc::space()
                      //             .append(RcDoc::as_string(": code _ _"))
                      //             .append(RcDoc::space())
                      //             .append(make_paren(tau)),
                      //     }
                      // } else {
                      //     RcDoc::nil()
                      // })
    )))
    .nest(2)
    .append(if typ_after && !do_bind {
        match typ.clone() {
            None => RcDoc::nil(),
            Some(tau) => RcDoc::space()
                .append(RcDoc::as_string(":"))
                .append(RcDoc::space())
                .append(tau),
        }
    } else {
        RcDoc::nil()
    })
    .append(if toplevel {
        RcDoc::as_string(".")
    } else {
        RcDoc::space()
            .append(if do_bind {
                RcDoc::as_string(";;")
            } else {
                RcDoc::as_string("in")
            })
            .append(RcDoc::line())
    })
    .append(if do_bind {
        if let Some(_) = typ.clone() {
            make_let_binding(
                pat.clone(),
                typ.clone(),
                typ_after.clone(),
                pat.clone(),
                false,
                false,
            )
        } else {
            RcDoc::nil()
        }
    } else {
        RcDoc::nil()
    })
}

fn code_block_wrap<'a>(
    expr: RcDoc<'a, ()>,
    location_vars: Option<RcDoc<'a, ()>>,
    result_typ: Option<RcDoc<'a, ()>>,
) -> RcDoc<'a, ()> {
    make_paren(
        RcDoc::as_string("{code ")
            .append(expr)
            .append(" } ")
            .append(RcDoc::as_string(":"))
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
    typ: Option<RcDoc<'a, ()>>,
    fun_pat: RcDoc<'a, ()>,
    fun_body: RcDoc<'a, ()>,
    smv_bind: ScopeMutableVars,
    smv_fun: ScopeMutableVars,
) -> RcDoc<'a, ()> {
    let local_vars_bind = list_of_loc_vars(smv_bind);
    let local_vars_fun = list_of_loc_vars(smv_fun);

    RcDoc::as_string("ChoiceEqualityMonad.bind_code (M := ")
        .append(match typ {
            Some(a) => a,
            None => RcDoc::as_string("_"),
        })
        .append(RcDoc::as_string(") (L1 := "))
        .append(local_vars_bind.clone())
        .append(RcDoc::as_string(") (L2 := "))
        .append(local_vars_fun.clone())
        .append(RcDoc::as_string(") (is_true0 := _)"))
        .append(RcDoc::space())
        .append(make_paren(expr))
        .append(RcDoc::space())
        .append(make_paren(
            RcDoc::as_string("fun")
                .append(RcDoc::space())
                .append(fun_pat)
                .append(RcDoc::as_string(" =>"))
                .append(RcDoc::softline())
                .append(fun_body), // code_block_wrap(, Some(local_vars_fun), None)
        ))
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

fn translate_literal<'a>(lit: Literal) -> RcDoc<'a, ()> {
    match lit {
        Literal::Unit => RcDoc::as_string("tt"),
        Literal::Bool(true) => RcDoc::as_string("true"),
        Literal::Bool(false) => RcDoc::as_string("false"),
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

#[derive(Debug)]
enum FuncPrefix {
    Regular,
    Array(ArraySize, BaseTyp),
    Seq(BaseTyp),
    NatMod(String, usize), // Modulo value, number of bits for the encoding,
}

fn translate_prefix_for_func_name<'a>(
    prefix: BaseTyp,
    top_ctx: &'a TopLevelContext,
) -> (RcDoc<'a, ()>, FuncPrefix) {
    match prefix {
        BaseTyp::Bool => panic!(), // should not happen
        BaseTyp::Unit => panic!(), // should not happen
        BaseTyp::UInt8 => (RcDoc::as_string("pub_uint8"), FuncPrefix::Regular),
        BaseTyp::Int8 => (RcDoc::as_string("pub_int8"), FuncPrefix::Regular),
        BaseTyp::UInt16 => (RcDoc::as_string("pub_uint16"), FuncPrefix::Regular),
        BaseTyp::Int16 => (RcDoc::as_string("pub_int16"), FuncPrefix::Regular),
        BaseTyp::UInt32 => (RcDoc::as_string("pub_uint32"), FuncPrefix::Regular),
        BaseTyp::Int32 => (RcDoc::as_string("pub_int32"), FuncPrefix::Regular),
        BaseTyp::UInt64 => (RcDoc::as_string("pub_uint64"), FuncPrefix::Regular),
        BaseTyp::Int64 => (RcDoc::as_string("pub_int64"), FuncPrefix::Regular),
        BaseTyp::UInt128 => (RcDoc::as_string("pub_uint128"), FuncPrefix::Regular),
        BaseTyp::Int128 => (RcDoc::as_string("pub_int128"), FuncPrefix::Regular),
        BaseTyp::Usize => (RcDoc::as_string("uint_size"), FuncPrefix::Regular),
        BaseTyp::Isize => (RcDoc::as_string("int_size"), FuncPrefix::Regular),
        BaseTyp::Str => (RcDoc::as_string("string"), FuncPrefix::Regular),
        BaseTyp::Enum(_cases, _type_args) => {
            panic!("Should not happen")
        }
        BaseTyp::Seq(inner_ty) => (
            RcDoc::as_string(SEQ_MODULE),
            FuncPrefix::Seq(inner_ty.as_ref().0.clone()),
        ),
        BaseTyp::Array(size, inner_ty) => (
            RcDoc::as_string(ARRAY_MODULE),
            FuncPrefix::Array(size.0.clone(), inner_ty.as_ref().0.clone()),
        ),
        BaseTyp::Named(ident, _) => {
            // if the type is an array, we should print the Seq module instead
            let name = &ident.0;
            match top_ctx.typ_dict.get(name) {
                Some((alias_typ, DictEntry::Array))
                | Some((alias_typ, DictEntry::Alias))
                | Some((alias_typ, DictEntry::NaturalInteger)) => {
                    translate_prefix_for_func_name((alias_typ.1).0.clone(), top_ctx)
                }
                // TODO: doesn't work if the alias uses a definition from another library
                // Needs fixing in the frontend
                _ => (
                    translate_ident_str(name.string.clone()),
                    FuncPrefix::Regular,
                ),
            }
        }
        BaseTyp::Variable(_) => panic!(), // shoult not happen
        BaseTyp::Tuple(_) => panic!(),    // should not happen
        BaseTyp::NaturalInteger(_, modulo, bits) => (
            RcDoc::as_string(NAT_MODULE),
            FuncPrefix::NatMod(modulo.0.clone(), bits.0.clone()),
        ),
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
                        FuncPrefix::Array(_, _) | FuncPrefix::Seq(_) => {
                            additional_args.push(RcDoc::as_string("default"));
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
                        let codegen_id: usize = {
                            let c_id = fresh_codegen_id();
                            // id_map.insert(id, c_id); // TODO: should this be inserted? (no need)
                            c_id
                        };

                        let temp_name = translate_ident_str(format!("{}_{}", "temp", codegen_id));

                        let temp_ass: RcDoc<'a, ()> = make_let_binding(
                            temp_name.clone(),
                            Some(translate_base_typ(BaseTyp::Seq(base_ty))),
                            false,
                            RcDoc::as_string("array_to_seq (")
                                .append(args[position].clone())
                                .append(RcDoc::as_string(")")),
                            false,
                            !inline,
                        );
                        args_ass.push(temp_ass);

                        args[position] = temp_name;
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

            (
                ass,
                make_paren(trans_e1)
                    .append(RcDoc::space())
                    .append(translate_binop(op, op_typ.as_ref().unwrap(), top_ctx))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .group(),
            )
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
                make_tuple(trans_iter),
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

            let codegen_id: usize = {
                let c_id = fresh_codegen_id();
                // id_map.insert(id, c_id); // TODO: should this be inserted? (no need)
                c_id
            };
            let temp_name = translate_ident_str(format!("{}_{}", "temp", codegen_id));

            let temp_ass: RcDoc<'a, ()> = make_let_binding(
                temp_name.clone(),
                func_ret_ty.map(|ret_ty| translate_base_typ(ret_ty)),
                false,
                fun_expr,
                false,
                !inline,
            );
            ass.push(temp_ass);

            (ass, temp_name)
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

                let codegen_id: usize = {
                    let c_id = fresh_codegen_id();
                    // id_map.insert(id, c_id); // TODO: should this be inserted? (no need)
                    c_id
                };
                let temp_name = translate_ident_str(format!("{}_{}", "temp", codegen_id));

                let temp_ass: RcDoc<'a, ()> = make_let_binding(
                    temp_name.clone(),
                    func_ret_ty.clone().map(|ret_ty| translate_base_typ(ret_ty)),
                    false,
                    method_call_expr,
                    false,
                    !inline,
                );
                ass.push(temp_ass);

                (ass, temp_name)
            }
        }
        Expression::ArrayIndex(x, e2, typ) => {
            let e2 = e2.0;
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);

            let (ass_e2, trans_e2) = translate_expression(e2, top_ctx, inline);

            (
                ass_e2,
                array_or_seq
                    .append(RcDoc::as_string("_index"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_ident(x.0.clone())))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2)),
            )
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
                            .append(make_paren(
                                make_let_binding(
                                    RcDoc::as_string("l"),
                                    None,
                                    false,
                                    trans,
                                    false,
                                    false,
                                )
                                .append(RcDoc::space())
                                .append(RcDoc::as_string("l")),
                            ))
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

// taken from rustspec_to_fstar
fn array_or_seq<'a>(t: Typ, top_ctxt: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match &(t.1).0 {
        BaseTyp::Seq(_) => RcDoc::as_string("seq"),
        BaseTyp::Named(id, None) => {
            let name = &id.0;
            match top_ctxt.typ_dict.get(name) {
                Some((new_t, dict_entry)) => match dict_entry {
                    DictEntry::Alias => array_or_seq(new_t.clone(), top_ctxt),
                    DictEntry::Enum => panic!("should not happen"),
                    DictEntry::Array => {
                        match &(new_t.1).0 {
                            BaseTyp::Array(_, _) => RcDoc::as_string("array"),
                            _ => panic!(), // shouldd not happen
                        }
                    }
                    DictEntry::NaturalInteger => panic!("should not happen"),
                },
                None => panic!("should not happen"),
            }
        }
        BaseTyp::Named(_, Some(_)) => panic!("should not happen"),
        BaseTyp::Array(_, _) => RcDoc::as_string("array"),
        _ => panic!("should not happen"),
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
                Some(smv_bind) => bind_code(
                    code_block_wrap(
                        RcDoc::as_string("@pkg_core_definition.ret _ ").append(trans_expr),
                        None,
                        None,
                    ),
                    None,
                    match pat.clone() {
                        Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
                        _ => RcDoc::nil(),
                    }
                    .append(translate_pattern_tick(pat.clone())),
                    code_block_wrap(trans_stmt, None, None),
                    smv_bind,
                    smv.clone(),
                ),
                None => if let Pattern::IdentPat(_i, true) = pat.clone() {
                    make_put_binding(
                        match pat.clone() {
                            Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
                            _ => RcDoc::nil(),
                        }
                        .append(translate_pattern_tick(pat.clone())),
                        typ.map(|(typ, _)| translate_typ(typ)),
                        match pat.clone() {
                            Pattern::SingleCaseEnum(_, _) | Pattern::Tuple(_) => true,
                            _ => false,
                        },
                        trans_expr,
                    )
                } else {
                    make_let_binding(
                        match pat.clone() {
                            Pattern::SingleCaseEnum(_, _) => RcDoc::as_string("'"),
                            _ => RcDoc::nil(),
                        }
                        .append(translate_pattern_tick(pat.clone())),
                        typ.map(|(typ, _)| translate_typ(typ)),
                        match pat.clone() {
                            Pattern::SingleCaseEnum(_, _) | Pattern::Tuple(_) => true,
                            _ => false,
                        },
                        trans_expr,
                        false,
                        false,
                    )
                }
                .append(trans_stmt),
            };

            ass_expr
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(expr)
        }
        Statement::Reassignment((x, _), (e1, _), question_mark) => {
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = match question_mark {
                Some(smv_bind) => bind_code(
                    trans_e1,
                    None,
                    translate_ident(x.clone()),
                    code_block_wrap(trans_stmt, None, None),
                    smv_bind,
                    smv.clone(),
                ),
                None => make_get_binding(translate_ident(x.clone()), None, false)
                    .append(RcDoc::line())
                    .append(make_put_binding(
                        translate_ident(x.clone()),
                        None,
                        false,
                        trans_e1,
                    ))
                    .append(RcDoc::hardline())
                    .append(trans_stmt),
            };

            ass_e1
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(expr)
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.clone().unwrap(), top_ctx);
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2.clone(), top_ctx, inline);

            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = match question_mark {
                Some(smv_bind) => bind_code(
                    trans_e2,
                    None,
                    RcDoc::as_string("_temp"),
                    make_let_binding(
                        translate_ident(x.clone()),
                        None,
                        false,
                        array_or_seq
                            .append(RcDoc::as_string("_upd"))
                            .append(RcDoc::space())
                            .append(translate_ident(x.clone()))
                            .append(RcDoc::space())
                            .append(make_paren(trans_e1))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("_temp")),
                        false,
                        false,
                    )
                    .append(RcDoc::hardline())
                    .append(trans_stmt),
                    smv_bind,
                    smv.clone(),
                ),
                None => {
                    let array_upd_payload = array_or_seq
                        .append(RcDoc::as_string("_upd"))
                        .append(RcDoc::space())
                        .append(translate_ident(x.clone()))
                        .append(RcDoc::space())
                        .append(make_paren(trans_e1))
                        .append(RcDoc::space())
                        .append(make_paren(trans_e2));

                    make_let_binding(
                        translate_ident(x.clone()),
                        typ.clone().map(|(_, (x, _))| translate_base_typ(x)),
                        false, // TODO: merge into typ info and get from translate_base_typ
                        array_upd_payload,
                        false,
                        !inline,
                    )
                    .append(RcDoc::hardline())
                    .append(trans_stmt)
                }
            };

            (ass_e1.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                .append(ass_e2.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                .append(expr)
        }

        Statement::ReturnExp(e1, t1) => {
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);

            ass_e1
                .into_iter()
                .fold(RcDoc::nil(), |rc, x| rc.append(x))
                .append(RcDoc::as_string("@pkg_core_definition.ret "))
                .append(make_paren(match t1 {
                    Some((_, (x, _))) => translate_base_typ(x),
                    None => RcDoc::as_string("_"),
                }))
                .append(RcDoc::as_string(" ( "))
                .append(make_paren(trans_e1))
                .append(RcDoc::as_string(")"))
        }
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
                if b1_question_mark {
                    Some(b1.mutable_vars.clone())
                } else {
                    None
                },
            ));

            let (ass_cond, trans_cond) = translate_expression(cond.clone(), top_ctx, inline);
            let block_1 = translate_block(b1.clone(), true, top_ctx, inline);

            let else_expr = match b2.clone() {
                None => {
                    let trans_stmt = translate_statements(
                        [(mutated_info.stmt.clone(), DUMMY_SP.into())].iter(),
                        top_ctx,
                        inline,
                        smv.clone(),
                    );
                    RcDoc::space().append(make_paren(trans_stmt))
                }
                Some((mut b2, _)) => {
                    b2.stmts.push(add_ok_if_result(
                        mutated_info.stmt.clone(),
                        mutated_info.early_return_type.clone(),
                        if b2_question_mark {
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
                let local_vars_bind_1 = list_of_loc_vars(b1.mutable_vars.clone());
                let local_vars_bind_2 = match b2.clone() {
                    Some((b2, _)) => list_of_loc_vars(b2.mutable_vars.clone()),
                    _ => RcDoc::as_string("[]"),
                };
                let local_vars_fun = list_of_loc_vars(smv);

                RcDoc::as_string(
                    "if_bind_code", // "ifbnd"
                )
                .append(RcDoc::as_string(" (M := _) (Lx := "))
                .append(local_vars_bind_1.clone())
                .append(RcDoc::as_string(") (Ly := "))
                .append(local_vars_bind_2.clone())
                .append(RcDoc::as_string(") (L2 := "))
                .append(local_vars_fun.clone())
                .append(RcDoc::as_string(") (it1 := _) (it2 := _)"))
                .append(RcDoc::space())
                .append(make_paren(
                    trans_cond
                        .append(RcDoc::space())
                        .append(RcDoc::as_string(": bool_ChoiceEquality")),
                ))
                .append(RcDoc::line())
                .append(make_paren(if b1_question_mark {
                    block_1.clone()
                } else {
                    code_block_wrap(block_1.clone(), None, None)
                }))
                .append(RcDoc::line())
                .append(make_paren(match b2 {
                    None => code_block_wrap(else_expr, None, None),
                    Some(_) => {
                        if b2_question_mark {
                            else_expr
                        } else {
                            code_block_wrap(else_expr, None, None)
                        }
                    }
                }))
                .append(RcDoc::space())
                // .append(RcDoc::as_string(">> "))
                .append(RcDoc::as_string("(fun"))
                .append(RcDoc::space())
                .append(pat)
                .append(RcDoc::space())
                .append(RcDoc::as_string("=>"))
                .append(RcDoc::line())
                .append(code_block_wrap(trans_stmt, None, None))
                .append(RcDoc::as_string(")"))
            } else {
                let expr = RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(trans_cond.clone())
                    .append(RcDoc::as_string(":bool_ChoiceEquality"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("then"))
                    .append(RcDoc::space())
                    .append(make_paren(block_1.clone()))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("else"))
                    .append(else_expr);

                make_let_binding(pat, None, false, expr, false, !inline)
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
            b.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                mutated_info.early_return_type.clone(),
                if b_question_mark {
                    Some(b.mutable_vars.clone())
                } else {
                    None
                },
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

            // TODO: Add ass_e1 and ass_e2 correctly to loop expression !
            let (ass_e1, trans_e1) = translate_expression(e1.clone(), top_ctx, inline);
            let (ass_e2, trans_e2) = translate_expression(e2.clone(), top_ctx, inline);

            let block_expr = translate_block(b.clone(), true, top_ctx, inline);
            let trans_stmt = translate_statements(statements, top_ctx, inline, smv.clone());

            let expr = if b_question_mark {
                let local_vars_bind = list_of_loc_vars(b.mutable_vars.clone());
                let local_vars_fun = list_of_loc_vars(smv.clone());

                let loop_expr = RcDoc::as_string("foldi_bind_code")
                    .append(RcDoc::as_string(" (M := _) (L1 := "))
                    .append(local_vars_bind.clone())
                    .append(RcDoc::as_string(") (L2 := "))
                    .append(local_vars_fun.clone())
                    .append(RcDoc::as_string(") (is_true0 := _)"))
                    .append(RcDoc::space())
                    // RcDoc::as_string("foldibnd")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    // .append(RcDoc::space())
                    // .append(RcDoc::as_string("to"))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    // .append(RcDoc::space())
                    // .append(RcDoc::as_string("for"))
                    .append(RcDoc::space())
                    // .append(mut_tuple("".to_string()).clone())
                    .append(make_paren(
                        RcDoc::as_string("Ok ").append(mut_tuple("".to_string()).clone()),
                    ))
                    .append(RcDoc::space())
                    // .append(RcDoc::as_string(">>"))
                    // .append(RcDoc::space())
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
                    .append(block_expr)
                    .append(RcDoc::as_string(")"));

                bind_code(
                    loop_expr,
                    None,
                    if mutated_info.vars.0.iter().len() == 0 {
                        RcDoc::as_string("_")
                    } else {
                        mut_tuple("'".to_string()).clone()
                    }, // TODO: Issue here with patterns (eg. 'tt)
                    code_block_wrap(trans_stmt, None, None),
                    b.mutable_vars.clone(),
                    smv.clone(),
                )
            } else {
                let loop_expr = RcDoc::as_string("foldi")
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e2))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(fun"))
                    .append(RcDoc::space())
                    .append(match x {
                        Some((x, _)) => translate_ident(x.clone()),
                        None => RcDoc::as_string("_"),
                    })
                    .append(RcDoc::space())
                    .append(make_paren(
                        mut_tuple("'".to_string())
                            .clone()
                            .append(RcDoc::as_string(" : "))
                            .append(RcDoc::as_string("_")),
                    ))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("=>"))
                    .append(RcDoc::line())
                    .append(block_expr)
                    .append(RcDoc::as_string(")"))
                    .group()
                    .nest(2)
                    .append(RcDoc::line())
                    .append(mut_tuple("".to_string()).clone());

                make_let_binding(
                    mut_tuple("'".to_string()),
                    None,
                    false,
                    loop_expr,
                    false,
                    !inline,
                )
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

    RcDoc::as_string("path.sort leb [")
        .append(RcDoc::space())
        .append(RcDoc::intersperse(
            all.iter()
                .map(|(i, _)| translate_ident(i.clone()).append("_loc")),
            RcDoc::space()
                .append(RcDoc::as_string(";"))
                .append(RcDoc::space()),
        ))
        .append(RcDoc::as_string("]"))
}

fn fset_from_scope<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    let mut all = smvars.external_vars.clone();
    all.extend(locals.clone());

    if all.len() == 0 {
        RcDoc::as_string("fset.fset0")
    } else {
        RcDoc::as_string("fset ").append(make_paren(list_of_loc_vars(smvars)))
    }
}

fn locations_from_scope<'a>(smvars: ScopeMutableVars) -> RcDoc<'a, ()> {
    let locals = smvars.local_vars.clone();
    RcDoc::intersperse(
        locals.into_iter().map(|(i, typ)| {
            make_let_binding(
                translate_ident(i.clone()).append("_loc"),
                Some(RcDoc::as_string("Location")),
                false,
                match typ {
                    Some(typ) => translate_typ(typ),
                    None => RcDoc::as_string("_"),
                }
                .append(RcDoc::space())
                .append(RcDoc::as_string(": choice_type ;"))
                .append(RcDoc::space())
                .append(RcDoc::as_string(fresh_codegen_id()))
                .append(RcDoc::as_string("%nat")),
                true,
                false,
            )
        }),
        RcDoc::line(),
    )
}

fn fset_and_locations<'a>(smvars: ScopeMutableVars) -> (RcDoc<'a, ()>, RcDoc<'a, ()>) {
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
                Statement::ReturnExp(Expression::Lit(Literal::Unit), None), // todo typing info
                DUMMY_SP.into(),
            ));
        }
        (Some(_), _) => (),
    }

    let trans_stmt =
        translate_statements(statements.iter(), top_ctx, inline, b.mutable_vars.clone());
    let local_vars = fset_from_scope(b.mutable_vars);

    code_block_wrap(trans_stmt.group(), Some(make_paren(local_vars)), None)

    // RcDoc::as_string("{code")
    //     .append(RcDoc::line())
    //     .append(trans_stmt.group())
    //     .append(RcDoc::line())
    //     .append(RcDoc::as_string("}"))
    //     .append(RcDoc::space())
    //     .append(RcDoc::as_string(":"))
    //     .append(RcDoc::space())
    //     .append(RcDoc::as_string("code "))
    //     .append(make_paren(local_vars))
    //     .append(RcDoc::as_string(" [interface] _"))
}

fn translate_item<'a>(
    item: &'a DecoratedItem,
    top_ctx: &'a TopLevelContext,
    export_quick_check: bool,
) -> RcDoc<'a, ()> {
    match &item.item {
        Item::FnDecl((f, _), sig, (b, _)) => {
            let block_exprs = translate_block(b.clone(), false, top_ctx, false);
            let (block_vars, block_var_loc_defs) = fset_and_locations(sig.mutable_vars.clone());

            block_var_loc_defs
                .append(RcDoc::line())
                .append(RcDoc::as_string("Program "))
                .append(
                    make_let_binding(
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
                            .append(RcDoc::as_string(": code"))
                            .append(RcDoc::space())
                            .append(make_paren(block_vars))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("[interface]"))
                            .append(RcDoc::space())
                            .append(make_paren(
                                RcDoc::as_string("@ct")
                                    .append(RcDoc::space())
                                    .append(make_paren(translate_base_typ(sig.ret.0.clone())))
                            ))
                            .group(),
                        None,
                        false,
                    block_exprs.group(),
                    true,
                    false,
                    )
                ).append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))
            .append({
                if item.tags.0.contains(&"quickcheck".to_string()) {
                RcDoc::hardline()
                    .append(RcDoc::as_string("QuickChick"))
                    .append(RcDoc::space())
                    .append(make_paren(RcDoc::concat(
                        sig.args
                            .iter()
                            .map(|((x, _), (tau, _))| {
                                RcDoc::as_string("forAll g_")
                                    .append(translate_typ(tau.clone()))
                                    .append(RcDoc::space())
                                    .append("(")
                                    .append(RcDoc::as_string("fun"))
                                    .append(RcDoc::space())
                                    .append(translate_ident(x.clone()))
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string(":"))
                                    .append(RcDoc::space())
                                    .append(translate_typ(tau.clone()))
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string("=>"))
                            }))
                            .append(translate_ident(Ident::TopLevel(f.clone())))
                            .append(RcDoc::concat(sig.args.iter().map(|((x, _), (_, _))| {
                                        RcDoc::space()
                                        .append(translate_ident(x.clone()))
                                }
                            )))
                            .append(RcDoc::concat(sig.args.iter().map(|_| RcDoc::as_string(")")))),
                    ))
                    .append(RcDoc::as_string("."))
                    .append(RcDoc::hardline())
                    .group()
            } else {
                RcDoc::nil()
            }
        })
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
            .append(if export_quick_check {
                RcDoc::hardline()
                    .append(RcDoc::as_string("Global Instance"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("show_"))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("Show ("))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::as_string(") :="))
                    .group()
                    .append(RcDoc::line())
                    .append(RcDoc::as_string(" @Build_Show ("))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::as_string(")"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("(fun x =>"))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("match x with"))
                    .append(RcDoc::line())
                    .append(RcDoc::intersperse(
                        cases.into_iter().map(|(case_name, case_typ)| {
                            let name_ty = BaseTyp::Named(name.clone(), None);
                            translate_enum_case_name(
                                name_ty.clone(),
                                case_name.0.clone(),
                                false,
                            )
                                .append(RcDoc::space())
                                .append(match case_typ {
                                    None => RcDoc::nil(),
                                    Some(_) => RcDoc::as_string("a").append(RcDoc::space()),
                                })
                                .append(RcDoc::as_string("=>"))
                                .append(RcDoc::space())
                                .append(make_paren(
                                    RcDoc::as_string("\"")
                                        .append(
                                            translate_enum_case_name(
                                                name_ty.clone(),
                                                case_name.0.clone(),
                                                false
                                            )
                                        )
                                        .append(RcDoc::as_string("\""))
                                        .append(match case_typ {
                                            None => RcDoc::nil(),
                                            Some(_) => RcDoc::space().append(RcDoc::as_string("++ show a")),
                                        })
                                ))
                                .append(RcDoc::as_string("%string"))
                        }),
                        RcDoc::line().append(RcDoc::as_string("|")).append(RcDoc::space())))
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("end)."))
                    .nest(1)
                    .append(RcDoc::hardline())
                    .append(RcDoc::as_string("Definition"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("g_"))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("G ("))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::as_string(") := oneOf_ ("))
                    .append(match cases.into_iter().next() {
                        Some ((case_name, case_typ)) => {
                            let name_ty = BaseTyp::Named(name.clone(), None);
                            match case_typ {
                                None => RcDoc::as_string("returnGen "),
                                Some(_) => RcDoc::as_string("bindGen arbitrary (fun a => returnGen ("),
                            }
                            .append(
                                translate_enum_case_name(
                                    name_ty.clone(),
                                    case_name.0.clone(),
                                    false
                                ))
                                .append(match case_typ {
                                    None => RcDoc::nil(),
                                    Some(_) => RcDoc::as_string(" a))"),
                                })
                        }
                        None => RcDoc::nil(),
                    })
                    .append(RcDoc::as_string(") ["))
                    .append(RcDoc::intersperse(
                        cases.into_iter().map(|(case_name, case_typ)| {
                            let name_ty = BaseTyp::Named(name.clone(), None);
                            match case_typ {
                                None => RcDoc::as_string("returnGen "),
                                Some(_) => RcDoc::as_string("bindGen arbitrary (fun a => returnGen ("),
                            }
                            .append(
                                translate_enum_case_name(
                                    name_ty.clone(),
                                    case_name.0.clone(),
                                    false,
                                ))
                                .append(match case_typ {
                                    None => RcDoc::nil(),
                                    Some(_) => RcDoc::as_string(" a))"),
                                })
                        }),
                        RcDoc::as_string(";")))
                    .append(RcDoc::as_string("]."))
                    .append(RcDoc::hardline())
                    .append(RcDoc::as_string("#[global] Instance"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("gen_"))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("Gen ("))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::as_string(") := Build_Gen"))
                    .append(RcDoc::space())
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("g_"))
                    .append(translate_ident(Ident::TopLevel(name.0.clone())))
                    .append(RcDoc::as_string("."))
                    .append(RcDoc::hardline())
             } else {
                 RcDoc::nil()
            }),
        Item::ArrayDecl(name, size, cell_t, index_typ) => {
            let (ass_size_0, trans_size_0) = translate_expression(size.0.clone(), top_ctx, false);
            RcDoc::as_string("Definition")
            .append(RcDoc::space())
            .append(translate_ident(Ident::TopLevel(name.0.clone())))
            .append(RcDoc::space())
            .append(RcDoc::as_string(":="))
            .group()
                .append(ass_size_0.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x)))
                .append(
                RcDoc::line()
                    .append(RcDoc::as_string("nseq"))
                    .append(RcDoc::space())
                    .append(make_paren(translate_base_typ(cell_t.0.clone())))
                    .append(RcDoc::space())
                    .append(make_paren(trans_size_0.clone()))
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
                        false,
                        RcDoc::as_string("nat_mod")
                            .append(RcDoc::space())
                            .append(make_paren(trans_size_0.clone())),
                        true,
                        false,
                    ))
                    .append(RcDoc::hardline())
                    .append(make_uint_size_coercion(translate_ident(Ident::TopLevel(
                        index_typ.0.clone(),
                    )))),
            })
        }
        Item::ConstDecl(name, ty, e) => {
            let (ass_e_0, trans_e_0) = translate_expression(e.0.clone(), top_ctx, true);
            make_let_binding(
                translate_ident(Ident::TopLevel(name.0.clone())),
                Some(// RcDoc::as_string("code")
                     // .append(RcDoc::space())
                     // .append(RcDoc::as_string("fset.fset0"))
                     // .append(RcDoc::space())
                     // .append(RcDoc::as_string("[interface]"))
                     // .append(RcDoc::space())
                     // .append(make_paren(
                     //     RcDoc::as_string("@ct")
                     //         .append(RcDoc::space())
                     //         .append(
                     make_paren(translate_base_typ(ty.0.clone()))
                     // )))
                ),
                false,
                // RcDoc::as_string("{code")
                //     .append(RcDoc::line())
                //     .append(
                        ass_e_0.into_iter().fold(RcDoc::nil(), |rc, x| rc.append(x))// )
                    // .append("pkg_core_definition.ret ")
                    .append(make_paren(trans_e_0))
                    // .append(RcDoc::line())
                    // .append(RcDoc::as_string("}"))
                    ,
                true,
                false,
            )
        },
        Item::NaturalIntegerDecl(nat_name, _secrecy, canvas_size, info) => {
            let canvas_size = match &canvas_size.0 {
                Expression::Lit(Literal::Usize(size)) => size,
                _ => panic!(), // should not happen by virtue of typchecking
            };
            let canvas_size_bytes = RcDoc::as_string(format!("{}", (canvas_size + 7) / 8));
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
                    .append(if export_quick_check {
                        RcDoc::hardline()
                            .append(RcDoc::as_string("Instance"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("show_"))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("Show ("))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string(") := Build_Show ("))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string(") (fun x => show (GZnZ.val "))
                            .append(RcDoc::as_string("_"))
                            .append(RcDoc::as_string(" x))."))
                            .append(RcDoc::hardline())
                            .append(RcDoc::as_string("Definition"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("g_"))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("G ("))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string(") := @bindGen Z ("))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string(
                                ") (arbitrary) (fun x => returnGen (@Z_in_nat_mod ",
                            ))
                            .append(RcDoc::as_string("_"))
                            .append(RcDoc::as_string(" x))."))
                            .append(RcDoc::hardline())
                            .append(RcDoc::as_string("Instance"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("gen_"))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("Gen ("))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string(") := Build_Gen"))
                            .append(RcDoc::space())
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string("g_"))
                            .append(translate_ident(Ident::TopLevel(nat_name.0.clone())))
                            .append(RcDoc::as_string("."))
                            .append(RcDoc::hardline())
                    } else {
                        RcDoc::nil()
                    }),
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
                .append(if export_quick_check {
                    match ty.clone() {
                        BaseTyp::Tuple(args) => {
                    RcDoc::hardline()
                        .append(RcDoc::as_string("Instance"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("show_"))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("Show ("))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::as_string(") :="))
                        .append(RcDoc::line())
                        .append(
                            RcDoc::as_string("Build_Show")
                                    .append(RcDoc::space())
                                    .append(translate_ident(Ident::TopLevel(ident.clone())))
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string("(fun x =>"))
                                    .append(RcDoc::line())
                                    .append(RcDoc::concat((0..args.len() - 1).map(|n| {
                                        RcDoc::as_string("let (x, x")
                                            .append(RcDoc::as_string(n.to_string()))
                                            .append(RcDoc::as_string(") := x in"))
                                            .append(RcDoc::line())
                                    })))
                                .append(make_paren(
                                    RcDoc::as_string("(\"(\") ++ (")
                                        .append(RcDoc::as_string("(show x) ++ ("))
                                        .append(RcDoc::concat((0..args.len() - 1).map(|n| {
                                            RcDoc::as_string(
                                                "(\",\") ++ ((show x",
                                            )
                                                .append(RcDoc::as_string(n.to_string()))
                                                .append(RcDoc::as_string(") ++ ("))
                                        })))
                                        .append(RcDoc::as_string("\")\")"))
                                        .append(RcDoc::concat((0..args.len() - 1).map(|_| {
                                            RcDoc::as_string("))")
                                        })))
                                        .append(RcDoc::as_string("))"))
                                ))
                                .append(RcDoc::as_string("%string"))
                                .group()
                                .nest(2)
                        )
                        .append(RcDoc::as_string("."))
                        .group()
                        .append(RcDoc::hardline())
                        .append(RcDoc::as_string("Definition"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("g_"))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("G ("))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::as_string(") :="))
                        .append(RcDoc::line())
                        .append(match ty.clone() {
                            BaseTyp::Tuple(args) => {
                                let answer =
                                    RcDoc::concat(args.clone().into_iter().enumerate()
                                        .map (|(n, (arg, _))| {
                                            RcDoc::as_string(
                                                "bindGen arbitrary (fun x",
                                            )
                                                .append(RcDoc::as_string(n.to_string()))
                                                .append(RcDoc::space())
                                                .append(RcDoc::as_string(":"))
                                                .append(RcDoc::space())
                                                .append(translate_base_typ(arg))
                                                .append(RcDoc::space())
                                                .append(RcDoc::as_string("=>"))
                                                .append(RcDoc::line())
                                        }));
                                answer
                                    .append(RcDoc::as_string("returnGen (x0"))
                                    .append(RcDoc::concat((1..args.len()).map(|n| {
                                        RcDoc::as_string(",")
                                            .append(RcDoc::as_string("x"))
                                            .append(RcDoc::as_string(n.to_string()))
                                    })))
                                    .append(RcDoc::as_string(")"))
                                    .append(RcDoc::concat(
                                        (0..args.len()).map(|_| {
                                            RcDoc::as_string(")")
                                        }))
                                    )
                                    .group()
                                    .nest(2)
                            }
                            _ => RcDoc::nil(),
                        })
                        .append(RcDoc::as_string("."))
                        .group()
                        .append(RcDoc::hardline())
                        .append(RcDoc::as_string("Instance"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("gen_"))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string(":"))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("Gen ("))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::as_string(") := Build_Gen"))
                        .append(RcDoc::space())
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("g_"))
                        .append(translate_ident(Ident::TopLevel(ident.clone())))
                        .append(RcDoc::as_string("."))
                        .group()
                                .append(RcDoc::hardline())
                            }
                        _ => RcDoc::nil(),
                    }
                } else {
                    RcDoc::nil()
                })
        }
    }
}

fn translate_program<'a>(
    p: &'a Program,
    top_ctx: &'a TopLevelContext,
    export_quick_check: bool,
) -> RcDoc<'a, ()> {
    RcDoc::concat(p.items.iter().map(|(i, _)| {
        translate_item(i, top_ctx, export_quick_check)
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
    let export_quick_check = p
        .items
        .iter()
        .any(|i| i.0.tags.0.contains(&"quickcheck".to_string()));
    write!(
        file,
        "(** This file was automatically generated using Hacspec **)\n\
         From Crypt Require Import choice_type Package Prelude.\n\
         Import PackageNotation.\n\
         From extructures Require Import ord fset.\n\
         From CoqWord Require Import ssrZ word.\n\
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
         Require Import Hacspec_Lib.\n\
         \n\
         Open Scope hacspec_scope.\n\
         {}\n\n\
         Obligation Tactic :=\n\
         (intros ; do 2 ssprove_valid'_2) ||\n\
         (try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)\n\
         \n",
        if export_quick_check {
            "From QuickChick Require Import QuickChick.\n\
             Require Import QuickChickLib.\n"
        } else {
            ""
        }
    )
    .unwrap();
    translate_program(p, top_ctx, export_quick_check)
        .render(width, &mut w)
        .unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
