use crate::name_resolution::TopLevelContext;
use crate::rustspec::*;
use crate::rustspec_to_coq_base::*;
use crate::rustspec_to_coq_ssprove_pure;
use crate::rustspec_to_coq_ssprove_state;
use crate::rustspec_to_coq_ssprove_state::translate_base_typ;
use core::slice::Iter;
use itertools::Itertools;
use pretty::RcDoc;
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use std::fs::File;
use std::io::Write;
use std::path;

fn translate_constructor<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    RcDoc::as_string(enum_name.string)
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
                        .map(|(x, _)| rustspec_to_coq_ssprove_state::translate_base_typ(x)),
                    RcDoc::space(),
                ))
            } else {
                RcDoc::nil()
            }),
        },
        _ => panic!("should not happen"),
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
        Pattern::EnumCase(ty_name, name, None) => {
            translate_enum_case_name(ty_name, name.0.clone(), false)
        }
        Pattern::EnumCase(ty_name, name, Some(inner_pat)) => {
            translate_enum_case_name(ty_name, name.0.clone(), false)
                .append(RcDoc::space())
                .append(make_paren(translate_pattern(inner_pat.0)))
        }
        Pattern::IdentPat(x, _) => translate_ident(x.clone()),
        Pattern::LiteralPat(x) => translate_literal(x.clone()),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => make_tuple(pats.into_iter().map(|(pat, _)| translate_pattern(pat))),
    }
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
        Literal::UnspecifiedInt(_) => panic!("Got a `UnspecifiedInt` literal: those should have been resolved into concrete types during the typechecking phase"),
        Literal::Str(msg) => RcDoc::as_string(format!("\"{}\"", msg)),
    }
}

fn make_let_binding<'a>(
    pat: Pattern,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
    monad_bind: bool,
    early_return_typ: Option<CarrierTyp>,
) -> RcDoc<'a, ()> {
    let mutable = if let Pattern::IdentPat(_, true) = pat.clone() {
        true
    } else {
        false
    };
    RcDoc::as_string("letb")
        .append(if monad_bind {
            RcDoc::as_string("nd")
                .append(if mutable {
                    RcDoc::as_string("m")
                } else {
                    RcDoc::nil()
                })
                .append(make_paren(match early_return_typ.clone() {
                    Some(CarrierTyp::Result(_, (c, _))) => {
                        RcDoc::as_string("ChoiceEqualityMonad.result_bind_both ")
                            .append(rustspec_to_coq_ssprove_state::translate_base_typ(c))
                    }
                    Some(CarrierTyp::Option(_)) => {
                        RcDoc::as_string("ChoiceEqualityMonad.option_bind_both")
                    }
                    None => RcDoc::as_string("_"),
                }))
        } else if mutable {
            RcDoc::as_string("m")
        } else {
            RcDoc::nil()
        })
        .append(RcDoc::space())
        .append(
            match typ.clone() {
                None => translate_pattern_tick(pat.clone()),
                Some(tau) => translate_pattern_tick(pat.clone())
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(tau),
            }
            .group(),
        )
        .append(RcDoc::space())
        .append(if mutable && !monad_bind {
            RcDoc::as_string("loc(")
                .append(RcDoc::space())
                .append(translate_pattern(pat.clone()))
                .append(RcDoc::as_string("_loc"))
                .append(RcDoc::space())
                .append(RcDoc::as_string(")"))
                .append(RcDoc::space())
        } else {
            RcDoc::nil()
        })
        .append(RcDoc::as_string(":="))
        .group()
        .append(RcDoc::line().append(expr.group()))
        .nest(2)
        .append(RcDoc::space())
        .append(RcDoc::as_string("in"))
}

fn translate_expression<'a>(e: Expression, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match e {
        Expression::MonadicLet(..) => panic!("TODO: Coq support for Expression::MonadicLet"),
        Expression::QuestionMark(..) => {
            // TODO: eliminiate this `panic!` with nicer types (See issue #303)
            panic!("[Expression::QuestionMark] nodes should have been eliminated before printing.")
        }
        Expression::Binary((op, _), e1, e2, op_typ) => {
            make_paren(translate_expression((*e1).0, top_ctx))
                .append(RcDoc::space())
                .append(translate_binop(
                    RcDoc::as_string("."),
                    op,
                    op_typ.as_ref().unwrap(),
                    top_ctx,
                ))
                .append(RcDoc::space())
                .append(make_paren(translate_expression((*e2).0, top_ctx)))
        }
        Expression::MatchWith(arg, arms) => RcDoc::as_string("TODO match"),
        Expression::FieldAccessor(e1, field) => {
            unimplemented!()
        }
        Expression::EnumInject(enum_name, case_name, payload) => {
            let trans = match payload {
                None => RcDoc::nil(),
                Some(payload) => RcDoc::space().append(make_paren(translate_expression(
                    *payload.0.clone(),
                    top_ctx,
                ))),
            };

            translate_enum_case_name(enum_name.clone(), case_name.0.clone(), true).append(trans)
        }
        Expression::InlineConditional(cond, e_t, e_f) => RcDoc::as_string("if")
            .append(RcDoc::space())
            .append(RcDoc::as_string("is_pure (I := [interface])"))
            .append(RcDoc::space())
            .append(make_paren(translate_expression((*cond).0, top_ctx)))
            .append(RcDoc::line())
            .append(RcDoc::as_string("then"))
            .append(RcDoc::space())
            .append(translate_expression((*e_t).0, top_ctx))
            .append(RcDoc::line())
            .append(RcDoc::as_string("else"))
            .append(RcDoc::space())
            .append(translate_expression((*e_f).0, top_ctx)),
        Expression::Unary(op, e1, op_typ) => translate_unop(op, op_typ.as_ref().unwrap().clone())
            .append(RcDoc::space())
            .append(make_paren(translate_expression((*e1).0, top_ctx)))
            .group(),
        Expression::Lit(lit) => RcDoc::as_string("lift_to_both0")
            .append(RcDoc::space())
            .append(make_paren(translate_literal(lit.clone()))),
        Expression::Tuple(es) => {
            let iter = es
                .into_iter()
                .map(|(e, _)| translate_expression(e, top_ctx));
            match &iter.size_hint().1 {
                Some(0) => RcDoc::as_string("tt"),
                Some(1) => RcDoc::intersperse(iter, RcDoc::nil()), // TODO: less hacky solution
                _ => RcDoc::as_string("prod_b(")
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
        Expression::Named(p) => RcDoc::as_string("lift_to_both0")
            .append(RcDoc::space())
            .append(translate_ident(p.clone())),
        Expression::FuncCall(prefix, name, args, arg_types) => {
            let (func_name, additional_args, func_ret_ty, extra_info) =
                rustspec_to_coq_ssprove_pure::translate_func_name(
                    // TODO: what implementation?
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
        }
        Expression::MethodCall(sel_arg, sel_typ, (f, _), args, arg_types) => {
            if f.string == "clone" {
                // Then the self argument
                make_paren(translate_expression((sel_arg.0).0, top_ctx))
                    // And finally the rest of the arguments
                    .append(RcDoc::concat(args.into_iter().map(|((arg, _), _)| {
                        RcDoc::space().append(make_paren(translate_expression(arg, top_ctx)))
                    })))
            } else {
                let (func_name, additional_args, func_ret_ty, extra_info) =
                    rustspec_to_coq_ssprove_pure::translate_func_name(
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
            }
        }
        Expression::ArrayIndex(x, e2, typ) => {
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);

            let trans_e2 = translate_expression((*e2).0, top_ctx);

            array_or_seq
                .append(RcDoc::as_string("_index"))
                .append(RcDoc::space())
                .append(make_paren(translate_ident(x.0.clone())))
                .append(RcDoc::space())
                .append(make_paren(trans_e2))
        }
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
                        .append(rustspec_to_coq_ssprove_state::translate_base_typ(
                            inner_ty.clone(),
                        ))
                        .append(RcDoc::space())
                        .append(make_paren(make_list(args.into_iter().map(|(e, _)| {
                            make_paren(translate_expression(e, top_ctx))
                                .append(RcDoc::as_string(" : "))
                                .append(rustspec_to_coq_ssprove_state::translate_base_typ(
                                    inner_ty.clone(),
                                ))
                        }))))
                }
            }
        }
        Expression::IntegerCasting(x, new_t, old_t) => {
            {
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
                        let trans_x = translate_expression(x.0.clone(), top_ctx);

                        new_t_doc.append(RcDoc::space()).append(make_paren(
                            RcDoc::as_string("is_pure")
                                .append(RcDoc::space())
                                .append(make_paren(trans_x)),
                        ))
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
                        let trans_x = translate_expression(x.as_ref().0.clone(), top_ctx);

                        RcDoc::as_string("(fun x => lift_to_both0 (repr (unsigned x)))")
                            .append(make_paren(trans_x))
                            .group()
                        // RcDoc::as_string("@cast _")
                        //     .append(RcDoc::space())
                        //     .append(new_t_doc)
                        //     .append(RcDoc::space())
                        //     .append(RcDoc::as_string("_"))
                        //     .append(RcDoc::space())
                        //     .append(make_paren(trans_x))
                        //     .group()
                    }
                }
            }
        }
    }
}

fn translate_statements<'a>(
    mut statements: Iter<Spanned<Statement>>,
    top_ctx: &'a TopLevelContext,
    smv: ScopeMutableVars,
    function_dependencies: FunctionDependencies,
) -> RcDoc<'a, ()> {
    let s = match statements.next() {
        None => return RcDoc::nil(),
        Some(s) => s.clone(),
    };

    match s.0 {
        Statement::LetBinding((pat, _), typ, (expr, _), carrier, question_mark) => {
            make_let_binding(
                pat.clone(),
                typ.map(|(typ, _)| rustspec_to_coq_ssprove_state::translate_typ(typ)),
                translate_expression(expr.clone(), top_ctx),
                // carrier.is_some(),
                question_mark.is_some(),
                carrier,
            )
        }
        Statement::Reassignment((x, _), _x_typ, (e1, _), carrier, question_mark) => {
            make_let_binding(
                Pattern::IdentPat(x.clone(), true),
                None,
                translate_expression(e1.clone(), top_ctx),
                // carrier.is_some(),
                question_mark.is_some(),
                carrier,
            )
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), carrier, question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.clone().unwrap(), top_ctx);
            let trans_e1 = translate_expression(e1.clone(), top_ctx);
            let trans_e2 = translate_expression(e2.clone(), top_ctx);

            let expr = {
                let array_upd_payload = array_or_seq
                    .append(RcDoc::as_string("_upd"))
                    .append(RcDoc::space())
                    .append(translate_ident(x.clone()))
                    .append(RcDoc::space())
                    .append(make_paren(trans_e1))
                    .append(RcDoc::space())
                    .append(make_paren(
                        RcDoc::as_string("is_pure ").append(make_paren(trans_e2)),
                    ));

                make_let_binding(
                    Pattern::IdentPat(x.clone(), false), // TODO: is mutable false?
                    typ.clone()
                        .map(|(_, (x, _))| rustspec_to_coq_ssprove_state::translate_base_typ(x)),
                    array_upd_payload,
                    // carrier.is_some(),
                    question_mark.is_some(),
                    carrier,
                )
            };

            expr
        }
        Statement::ReturnExp(e1, _typ) => RcDoc::as_string("lift_scope")
            .append(RcDoc::space())
            .append(RcDoc::as_string("(H_loc_incl := _) (H_opsig_incl := _)"))
            .append(RcDoc::space())
            .append(make_paren(translate_expression(e1.clone(), top_ctx))),
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
                            Pattern::IdentPat(Ident::Local(i.clone()), i.mutable),
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
                if either_blocks_contains_question_mark {
                    mutated_info.early_return_type.clone()
                } else {
                    None
                },
            ));

            let trans_cond = translate_expression(cond.clone(), top_ctx);
            let block_1 = translate_block(b1.clone(), true, top_ctx);

            let else_expr = match b2.clone() {
                None => translate_statements(
                    vec![add_ok_if_result(
                        mutated_info.stmt.clone(),
                        if either_blocks_contains_question_mark {
                            mutated_info.early_return_type.clone()
                        } else {
                            None
                        },
                    )]
                    .iter(),
                    top_ctx,
                    smv.clone(),
                    function_dependencies.clone(),
                ),
                Some((mut b2, _)) => {
                    b2.stmts.push(add_ok_if_result(
                        mutated_info.stmt.clone(),
                        if either_blocks_contains_question_mark {
                            mutated_info.early_return_type.clone()
                        } else {
                            None
                        },
                    ));

                    let block2_expr = translate_block(b2.clone(), true, top_ctx);

                    RcDoc::space()
                        .append(RcDoc::as_string("lift_scope"))
                        .append(RcDoc::space())
                        .append(make_paren(RcDoc::as_string("L1 := ").append(
                            rustspec_to_coq_ssprove_state::fset_from_scope(b2.mutable_vars.clone()),
                        )))
                        .append(RcDoc::space())
                        .append(make_paren(RcDoc::as_string("L2 := ").append(
                            rustspec_to_coq_ssprove_state::fset_from_scope(smv.clone()),
                        )))
                        .append(RcDoc::space())
                        .append(make_paren(RcDoc::as_string("I1 := ").append(RcDoc::as_string("[interface]"))))
                        .append(RcDoc::space())
                        .append(make_paren(RcDoc::as_string("I2 := ").append(RcDoc::as_string("[interface]"))))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("(H_loc_incl := _) (H_opsig_incl := _)"))
                        .append(RcDoc::space())
                        .append(make_paren(block2_expr))
                }
            };

            let expr = RcDoc::as_string("if")
                .append(RcDoc::space())
                .append(trans_cond.clone())
                .append(RcDoc::space())
                .append(RcDoc::as_string(":bool_ChoiceEquality"))
                .append(RcDoc::line())
                .append(RcDoc::as_string("then"))
                .append(RcDoc::space())
                .append(RcDoc::as_string("lift_scope"))
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("L1 := ").append(
                    rustspec_to_coq_ssprove_state::fset_from_scope(b1.mutable_vars.clone()),
                )))
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("L2 := ").append(
                    rustspec_to_coq_ssprove_state::fset_from_scope(smv.clone()),
                )))
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("I1 := ").append(RcDoc::as_string("[interface]"))))
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("I2 := ").append(RcDoc::as_string("[interface]"))))
                .append(RcDoc::space())
                .append(RcDoc::as_string("(H_loc_incl := _) (H_opsig_incl := _)"))
                .append(RcDoc::space())
                .append(make_paren(block_1.clone()))
                .append(RcDoc::line())
                .append(RcDoc::as_string("else"))
                .append(RcDoc::space())
                .append(else_expr);

            make_let_binding(
                pat,
                None,
                expr,
                either_blocks_contains_question_mark,
                mutated_info.early_return_type.clone(), // TODO
            )
        }
        Statement::ForLoop(x, (e1, _), (e2, _), (mut b, _)) => {
            let mutated_info = b.mutated.clone().unwrap();
            let b_question_mark = *b.contains_question_mark.as_ref().unwrap();
            b.stmts.push(add_ok_if_result(
                mutated_info.stmt.clone(),
                if b_question_mark {
                    mutated_info.early_return_type.clone()
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

            make_let_binding(
                mut_tuple.clone(),
                None,
                if b_question_mark {
                    RcDoc::as_string("foldi_bind_both'")
                } else {
                    RcDoc::as_string("foldi_both'")
                }
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1, top_ctx)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2, top_ctx)))
                .append(RcDoc::space())
                .append(match mut_tuple.clone() {
                    Pattern::Tuple(_) => {
                        RcDoc::as_string("prod_ce").append(translate_pattern(mut_tuple.clone()))
                    }
                    _ => translate_pattern(mut_tuple.clone()),
                })
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("L := ").append(make_paren(
                    rustspec_to_coq_ssprove_state::fset_from_scope(smv.clone()),
                ))))
                .append(RcDoc::space())
                .append(make_paren(RcDoc::as_string("I := ").append(RcDoc::as_string("[interface]"))))
                .append(RcDoc::space())
                .append(make_paren(
                    RcDoc::as_string("fun")
                        .append(RcDoc::space())
                        .append(match x.clone() {
                            Some((x, _)) => translate_ident(x.clone()),
                            None => RcDoc::as_string("_"),
                        })
                        .append(RcDoc::space())
                        .append(translate_pattern_tick(mut_tuple.clone()))
                        .append(RcDoc::space())
                        .append(RcDoc::as_string("=>"))
                        .append(RcDoc::line())
                        .append(translate_block(b, true, top_ctx)),
                ))
                .group()
                .nest(2),
                b_question_mark,
                mutated_info.early_return_type.clone(),
            )
        }
    }
    .group()
    .append(RcDoc::line())
    .append(translate_statements(
        statements,
        top_ctx,
        smv,
        function_dependencies.clone(),
    ))
}

fn translate_block<'a>(
    b: Block,
    omit_extra_unit: bool,
    top_ctx: &'a TopLevelContext,
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
        b.mutable_vars.clone(),
        b.function_dependencies.clone(),
    );
    // let local_vars = fset_from_scope(b.mutable_vars);

    // code_block_wrap(
    trans_stmt.group() // , Some(make_paren(local_vars)), None)
}

fn translate_item<'a>(item: DecoratedItem, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match item.item.clone() {
        Item::FnDecl((f, _), sig, (b, _)) => {
            let (block_vars, block_var_loc_defs) =
                rustspec_to_coq_ssprove_state::fset_and_locations(sig.mutable_vars.clone());

            block_var_loc_defs.append({
                let block_exprs = translate_block(b.clone(), false, top_ctx);

                let interface = RcDoc::as_string("[interface]");

                let fun_inp_notation_0 = RcDoc::as_string("Notation")
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("\"'"))
                    .append(
                        translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::as_string("_inp")),
                    )
                    .append(RcDoc::as_string("'\""))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .append(make_paren(
                        if sig.args.is_empty() {
                            RcDoc::as_string("unit_ChoiceEquality")
                        } else {
                            RcDoc::intersperse(
                                sig.args.iter().map(|((_x, _), (tau, _))| {
                                    rustspec_to_coq_ssprove_state::translate_typ(tau.clone())
                                }),
                                RcDoc::space()
                                    .append(RcDoc::as_string("'×"))
                                    .append(RcDoc::space()),
                            )
                        }
                        .append(RcDoc::as_string(" : choice_type")),
                    ))
                    .append(RcDoc::as_string(" (in custom pack_type at level 2)."));

                let fun_inp_notation_1 = RcDoc::as_string("Notation")
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("\"'"))
                    .append(
                        translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::as_string("_inp")),
                    )
                    .append(RcDoc::as_string("'\""))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .append(make_paren(
                        if sig.args.is_empty() {
                            RcDoc::as_string("unit_ChoiceEquality")
                        } else {
                            RcDoc::intersperse(
                                sig.args.iter().map(|((_x, _), (tau, _))| {
                                    rustspec_to_coq_ssprove_state::translate_typ(tau.clone())
                                }),
                                RcDoc::space()
                                    .append(RcDoc::as_string("'×"))
                                    .append(RcDoc::space()),
                            )
                        }
                        .append(RcDoc::as_string(" : ChoiceEquality")),
                    ))
                    .append(RcDoc::as_string(" (at level 2)."));

                let fun_out_notation_0 = RcDoc::as_string("Notation")
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("\"'"))
                    .append(
                        translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::as_string("_out")),
                    )
                    .append(RcDoc::as_string("'\""))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .append(make_paren(
                        rustspec_to_coq_ssprove_state::translate_base_typ(sig.ret.0.clone())
                            .append(RcDoc::as_string(" : choice_type")),
                    ))
                    .append(RcDoc::as_string(" (in custom pack_type at level 2)."));

                let fun_out_notation_1 = RcDoc::as_string("Notation")
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("\"'"))
                    .append(
                        translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::as_string("_out")),
                    )
                    .append(RcDoc::as_string("'\""))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string(":="))
                    .append(make_paren(
                        rustspec_to_coq_ssprove_state::translate_base_typ(sig.ret.0.clone())
                            .append(RcDoc::as_string(" : ChoiceEquality")),
                    ))
                    .append(RcDoc::as_string(" (at level 2)."));

                let fun_ident_def = rustspec_to_coq_ssprove_state::make_definition(
                    RcDoc::as_string(f.clone().string.to_uppercase()),
                    Some(RcDoc::as_string("nat")),
                    RcDoc::as_string(fresh_codegen_id()),
                );

                let both_type = RcDoc::as_string("both")
                    .append(RcDoc::space())
                    .append(make_paren(block_vars.clone()))
                    .append(RcDoc::space())
                    .append(interface)
                    .append(RcDoc::space())
                    .append(make_paren(
                        rustspec_to_coq_ssprove_state::translate_base_typ(sig.ret.0.clone()), // translate_ident(Ident::TopLevel(f.clone())).append("_out")
                    ));

                let package_wraped_code_block = make_paren(
                    make_paren(block_exprs.group())
                        .append(RcDoc::space())
                        .append(":")
                        .append(RcDoc::space())
                        .append(both_type.clone()),
                );

                RcDoc::line()
                    .append(fun_inp_notation_0)
                    .append(RcDoc::line())
                    .append(fun_inp_notation_1)
                    .append(RcDoc::line())
                    .append(fun_out_notation_0)
                    .append(RcDoc::line())
                    .append(fun_out_notation_1)
                    .append(RcDoc::line())
                    .append(fun_ident_def)
                    .append(RcDoc::line())
                    // .append(RcDoc::as_string("Equations "))
                    .append(RcDoc::as_string("Program Definition "))
                    .append(rustspec_to_coq_ssprove_pure::make_definition_inner(
                        translate_ident(Ident::TopLevel(f.clone()))
                            .append(RcDoc::space())
                            .append(RcDoc::intersperse(
                                sig.args.iter().map(|((x, _), (tau, _))| {
                                    make_paren(
                                        translate_ident(x.clone())
                                            .append(RcDoc::space())
                                            .append(RcDoc::as_string(":"))
                                            .append(RcDoc::space())
                                            .append(
                                                rustspec_to_coq_ssprove_state::translate_base_typ(
                                                    tau.clone().1 .0,
                                                ),
                                            ),
                                    )
                                }),
                                RcDoc::space(),
                            ))
                            .append(RcDoc::line())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(both_type)
                            .group(),
                        None,
                        // translate_ident(Ident::TopLevel(f.clone()))
                        //     .append(RcDoc::as_string(" := "))
                        //     .append(
                        package_wraped_code_block.group(), // )
                    ))
                    .append(RcDoc::hardline().append(RcDoc::as_string("Fail Next Obligation.")))
            })
        }
        Item::EnumDecl(_, _) => rustspec_to_coq_ssprove_state::translate_item(item, top_ctx),
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
         Set Warnings \"-notation-overridden,-ambiguous-paths\".\n\
         From Crypt Require Import choice_type Package Prelude.\n\
         Import PackageNotation.\n\
         From extructures Require Import ord fset.\n\
         From mathcomp.word Require Import ssrZ word.\n\
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
