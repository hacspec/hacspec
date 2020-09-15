use crate::rustspec::*;

use crate::typechecker::{DictEntry, TypeDict};
use core::iter::IntoIterator;
use heck::SnakeCase;
use pretty::RcDoc;
use regex::Regex;
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;
use std::fs::File;
use std::io::Write;
use std::path;

const SEQ_MODULE: &'static str = "RSeq";

fn make_let_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
    toplevel: bool,
) -> RcDoc<'a, ()> {
    RcDoc::as_string("let")
        .append(RcDoc::space())
        .append(
            pat.append(match typ {
                None => RcDoc::nil(),
                Some(tau) => RcDoc::space()
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(tau),
            })
            .group(),
        )
        .append(RcDoc::space())
        .append(RcDoc::as_string("="))
        .group()
        .append(RcDoc::line().append(expr.group()))
        .nest(2)
        .append(if toplevel {
            RcDoc::nil()
        } else {
            RcDoc::line().append(RcDoc::as_string("in"))
        })
}

fn make_tuple<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
    RcDoc::as_string("(")
        .append(
            RcDoc::line_()
                .append(RcDoc::intersperse(
                    args.into_iter(),
                    RcDoc::as_string(",").append(RcDoc::line()),
                ))
                .group()
                .nest(2),
        )
        .append(RcDoc::line_())
        .append(RcDoc::as_string(")"))
        .group()
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
                        .append(RcDoc::as_string("&"))
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
        .append(RcDoc::line_().append(e).group().nest(2))
        .append(RcDoc::as_string(")"))
        .group()
}

fn make_begin_paren<'a>(e: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
    RcDoc::as_string("begin")
        .append(RcDoc::line().append(e).group().nest(2))
        .append(RcDoc::line())
        .append(RcDoc::as_string("end"))
}

fn translate_ident(x: &Ident) -> RcDoc<()> {
    let mut ident_str = match x {
        Ident::Original(s) => s.clone(),
        Ident::Hacspec(id, s) => format!("{}_{}", s, id.0),
    };
    let secret_int_regex = Regex::new(r"(U|I)\d{1,3}").unwrap();
    ident_str = secret_int_regex.replace_all(&ident_str, "s$0").to_string();
    let mut snake_case_ident = ident_str.to_snake_case();
    if snake_case_ident == "new" {
        snake_case_ident = "new_".to_string();
    }
    RcDoc::as_string(snake_case_ident)
}

fn translate_base_typ(tau: &BaseTyp) -> RcDoc<()> {
    match tau {
        BaseTyp::Unit => RcDoc::as_string("unit"),
        BaseTyp::Bool => RcDoc::as_string("bool"),
        BaseTyp::UInt8 => RcDoc::as_string("u8"),
        BaseTyp::Int8 => RcDoc::as_string("i8"),
        BaseTyp::UInt16 => RcDoc::as_string("u16"),
        BaseTyp::Int16 => RcDoc::as_string("i16"),
        BaseTyp::UInt32 => RcDoc::as_string("u32"),
        BaseTyp::Int32 => RcDoc::as_string("i32"),
        BaseTyp::UInt64 => RcDoc::as_string("u64"),
        BaseTyp::Int64 => RcDoc::as_string("i64"),
        BaseTyp::UInt128 => RcDoc::as_string("u128"),
        BaseTyp::Int128 => RcDoc::as_string("i128"),
        BaseTyp::Usize => RcDoc::as_string("usize"),
        BaseTyp::Isize => RcDoc::as_string("isize"),
        BaseTyp::Str => RcDoc::as_string("string"),
        BaseTyp::Seq(tau) => {
            let tau: &BaseTyp = &tau.0;
            RcDoc::as_string(format!("{}.seq", SEQ_MODULE))
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .group()
        }
        BaseTyp::Array(size, tau) => {
            let tau: &BaseTyp = &tau.0;
            RcDoc::as_string(format!("{}.lseq", SEQ_MODULE))
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .append(RcDoc::space())
                .append(RcDoc::as_string(match &size.0 {
                    ArraySize::Ident(id) => format!("{}", id),
                    ArraySize::Integer(i) => format!("{}", i),
                }))
                .group()
        }
        BaseTyp::Named(ident, args) => translate_ident(&ident.0).append(match args {
            None => RcDoc::nil(),
            Some(args) => RcDoc::space().append(RcDoc::intersperse(
                args.iter().map(|arg| translate_base_typ(&arg.0)),
                RcDoc::space(),
            )),
        }),
        BaseTyp::Variable(id) => RcDoc::as_string(format!("'t{}", id.0)),
        BaseTyp::Tuple(args) => make_typ_tuple(args.iter().map(|(arg, _)| translate_base_typ(arg))),
        BaseTyp::NaturalInteger(_, _) => unimplemented!(),
    }
}

fn translate_typ((_, (tau, _)): &Typ) -> RcDoc<()> {
    translate_base_typ(tau)
}

fn translate_literal(lit: &Literal) -> RcDoc<()> {
    match lit {
        Literal::Unit => RcDoc::as_string("()"),
        Literal::Bool(true) => RcDoc::as_string("true"),
        Literal::Bool(false) => RcDoc::as_string("false"),
        Literal::Int128(x) => RcDoc::as_string(format!("Int128.uint_to_t {}", x)),
        Literal::UInt128(x) => RcDoc::as_string(format!("UInt128.uint_to_t {}", x)),
        Literal::Int64(x) => RcDoc::as_string(format!("{}L", x)),
        Literal::UInt64(x) => RcDoc::as_string(format!("{}UL", x)),
        Literal::Int32(x) => RcDoc::as_string(format!("{}l", x)),
        Literal::UInt32(x) => RcDoc::as_string(format!("{}ul", x)),
        Literal::Int16(x) => RcDoc::as_string(format!("{}s", x)),
        Literal::UInt16(x) => RcDoc::as_string(format!("{}us", x)),
        Literal::Int8(x) => RcDoc::as_string(format!("{}y", x)),
        Literal::UInt8(x) => RcDoc::as_string(format!("{}uy", x)),
        Literal::Usize(x) => RcDoc::as_string(format!("{}ul", x)),
        Literal::Isize(x) => RcDoc::as_string(format!("{}l", x)),
        Literal::Str(msg) => RcDoc::as_string(format!("\"{}\"", msg)),
    }
}

fn translate_pattern(p: &Pattern) -> RcDoc<()> {
    match p {
        Pattern::IdentPat(x) => translate_ident(x),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => make_tuple(pats.iter().map(|(pat, _)| translate_pattern(pat))),
    }
}

fn translate_binop(op: &BinOpKind) -> RcDoc<()> {
    match op {
        BinOpKind::Sub => RcDoc::as_string("-"),
        BinOpKind::Add => RcDoc::as_string("+"),
        BinOpKind::Mul => RcDoc::as_string("*"),
        BinOpKind::Div => RcDoc::as_string("/"),
        BinOpKind::Rem => RcDoc::as_string("%"),
        BinOpKind::And => RcDoc::as_string("&&"),
        BinOpKind::Or => RcDoc::as_string("||"),
        BinOpKind::BitXor => RcDoc::as_string("^"),
        BinOpKind::BitAnd => RcDoc::as_string("&"),
        BinOpKind::BitOr => RcDoc::as_string("|"),
        BinOpKind::Shl => RcDoc::as_string("`shift_left`"),
        BinOpKind::Shr => RcDoc::as_string("`shift_right`"),
        BinOpKind::Eq => RcDoc::as_string("=="),
        BinOpKind::Lt => RcDoc::as_string("<"),
        BinOpKind::Le => RcDoc::as_string("<="),
        BinOpKind::Ne => RcDoc::as_string("!="),
        BinOpKind::Ge => RcDoc::as_string(">="),
        BinOpKind::Gt => RcDoc::as_string(">"),
    }
}

fn translate_unop(op: &UnOpKind) -> RcDoc<()> {
    match op {
        UnOpKind::Not => RcDoc::as_string("~"),
        UnOpKind::Neg => RcDoc::as_string("-"),
    }
}

fn translate_prefix_for_func_name<'a, 'b>(
    prefix: &'a BaseTyp,
    typ_dict: &'a TypeDict,
) -> (RcDoc<'a, ()>, Option<ArraySize>) {
    match prefix {
        BaseTyp::Bool => panic!(), // should not happen
        BaseTyp::Unit => panic!(), // should not happen
        BaseTyp::UInt8 => (RcDoc::as_string("RInt8"), None),
        BaseTyp::Int8 => (RcDoc::as_string("RInt8"), None),
        BaseTyp::UInt16 => (RcDoc::as_string("RUInt16"), None),
        BaseTyp::Int16 => (RcDoc::as_string("RInt16"), None),
        BaseTyp::UInt32 => (RcDoc::as_string("RUInt32"), None),
        BaseTyp::Int32 => (RcDoc::as_string("RInt32"), None),
        BaseTyp::UInt64 => (RcDoc::as_string("RUInt64"), None),
        BaseTyp::Int64 => (RcDoc::as_string("RInt64"), None),
        BaseTyp::UInt128 => (RcDoc::as_string("RUInt128"), None),
        BaseTyp::Int128 => (RcDoc::as_string("RInt128"), None),
        BaseTyp::Usize => (RcDoc::as_string("RUInt32"), None),
        BaseTyp::Isize => (RcDoc::as_string("RInt32"), None),
        BaseTyp::Str => (RcDoc::as_string("RString"), None),
        BaseTyp::Seq(_) => (RcDoc::as_string(SEQ_MODULE), None),
        BaseTyp::Array(size, _) => (RcDoc::as_string(SEQ_MODULE), Some(size.0.clone())),
        BaseTyp::Named(ident, _) => {
            // if the type is an array, we should print the Seq module instead
            match &ident.0 {
                Ident::Original(name) => match typ_dict.get(name) {
                    Some((alias_typ, DictEntry::Array)) | Some((alias_typ, DictEntry::Alias)) => {
                        translate_prefix_for_func_name(&(alias_typ.1).0, typ_dict)
                    }
                    _ => (RcDoc::as_string(name), None),
                },
                Ident::Hacspec(_, _) => panic!(), // should not happen
            }
        } // TODO: change with typ dict
        BaseTyp::Variable(_) => panic!(), // shoult not happen
        BaseTyp::Tuple(_) => panic!(),    // should not happen
        BaseTyp::NaturalInteger(_, _) => unimplemented!(),
    }
}

fn translate_func_name<'a>(
    prefix: &'a Option<Spanned<BaseTyp>>,
    name: &'a Ident,
    typ_dict: &'a TypeDict,
) -> RcDoc<'a, ()> {
    match prefix {
        None => translate_ident(name),
        Some((prefix, _)) => {
            let (module_name, array_size) = translate_prefix_for_func_name(prefix, typ_dict);
            let type_arg = match prefix {
                BaseTyp::Seq(tau) => Some(translate_base_typ(&tau.0)),
                BaseTyp::Array(_, tau) => Some(translate_base_typ(&tau.0)),
                _ => None,
            };
            let func_ident = translate_ident(name);
            module_name
                .append(RcDoc::as_string("."))
                .append(func_ident.clone())
                .append(if format!("{}", func_ident.pretty(0)) == "new_" {
                    match array_size {
                        None => RcDoc::nil(),
                        Some(ArraySize::Ident(s)) => RcDoc::space().append(RcDoc::as_string(s)),
                        Some(ArraySize::Integer(i)) => {
                            RcDoc::space().append(RcDoc::as_string(format!("{}ul", i)))
                        }
                    }
                } else {
                    RcDoc::nil()
                })
                .append(match type_arg {
                    None => RcDoc::nil(),
                    Some(arg) => RcDoc::space().append(RcDoc::as_string("#")).append(arg),
                })
        }
    }
}

fn translate_expression<'a>(e: &'a Expression, typ_dict: &'a TypeDict) -> RcDoc<'a, ()> {
    match e {
        Expression::Binary((op, _), ref e1, ref e2) => {
            let e1 = &e1.0;
            let e2 = &e2.0;
            translate_expression(e1, typ_dict)
                .append(RcDoc::space())
                .append(translate_binop(op))
                .append(RcDoc::space())
                .append(translate_expression(e2, typ_dict))
                .group()
        }
        Expression::Unary(op, e1) => {
            let e1 = &e1.0;
            translate_unop(op)
                .append(RcDoc::space())
                .append(translate_expression(e1, typ_dict))
                .group()
        }
        Expression::Lit(lit) => translate_literal(lit),
        Expression::Tuple(es) => make_tuple(
            es.into_iter()
                .map(|(e, _)| translate_expression(&e, typ_dict)),
        ),
        Expression::Named(p) => translate_ident(p),
        Expression::FuncCall(prefix, name, args) => translate_func_name(prefix, &name.0, typ_dict)
            .append(if args.len() > 0 {
                RcDoc::concat(args.iter().map(|((arg, _), _)| {
                    RcDoc::space().append(make_paren(translate_expression(arg, typ_dict)))
                }))
            } else {
                RcDoc::space().append(RcDoc::as_string("()"))
            }),
        Expression::MethodCall(sel_arg, _, (f, _), args) => translate_ident(f)
            .append(
                RcDoc::space().append(make_paren(translate_expression(&(sel_arg.0).0, typ_dict))),
            )
            .append(RcDoc::concat(args.iter().map(|((arg, _), _)| {
                RcDoc::space().append(make_paren(translate_expression(arg, typ_dict)))
            }))),
        Expression::ArrayIndex(x, e2) => {
            let e2 = &e2.0;
            RcDoc::as_string("array_index")
                .append(RcDoc::space())
                .append(make_paren(translate_ident(&x.0)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2, typ_dict)))
        }
        Expression::NewArray(_, _, args) => RcDoc::as_string(format!("{}.from_list", SEQ_MODULE))
            .append(RcDoc::space())
            .append(make_list(
                args.iter().map(|(e, _)| translate_expression(e, typ_dict)),
            )),
        Expression::IntegerCasting(_, _) => unimplemented!(),
    }
}

fn translate_statement<'a>(s: &'a Statement, typ_dict: &'a TypeDict) -> RcDoc<'a, ()> {
    match s {
        Statement::LetBinding((pat, _), typ, (expr, _)) => make_let_binding(
            translate_pattern(pat),
            typ.as_ref().map(|(typ, _)| translate_typ(typ)),
            translate_expression(expr, typ_dict),
            false,
        ),
        Statement::Reassignment((x, _), (e1, _)) => make_let_binding(
            translate_ident(x),
            None,
            translate_expression(e1, typ_dict),
            false,
        ),
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _)) => make_let_binding(
            translate_ident(x),
            None,
            RcDoc::as_string("array_upd")
                .append(RcDoc::space())
                .append(translate_ident(x))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1, typ_dict)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2, typ_dict))),
            false,
        ),
        Statement::ReturnExp(e1) => translate_expression(e1, typ_dict),
        Statement::Conditional((cond, _), (b1, _), b2, mutated) => {
            let mutated_info = mutated.as_ref().unwrap().as_ref();
            make_let_binding(
                make_tuple(mutated_info.vars.iter().map(|i| translate_ident(i))),
                None,
                RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(translate_expression(cond, typ_dict))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("then"))
                    .append(RcDoc::space())
                    .append(make_begin_paren(
                        translate_block(b1, true, typ_dict)
                            .append(RcDoc::hardline())
                            .append(translate_statement(&mutated_info.stmt, typ_dict)),
                    ))
                    .append(match b2 {
                        None => RcDoc::space()
                            .append(RcDoc::as_string("else"))
                            .append(RcDoc::space())
                            .append(make_begin_paren(translate_statement(
                                &mutated_info.stmt,
                                typ_dict,
                            ))),
                        Some((b2, _)) => RcDoc::space()
                            .append(RcDoc::as_string("else"))
                            .append(RcDoc::space())
                            .append(make_begin_paren(
                                translate_block(b2, true, typ_dict)
                                    .append(RcDoc::hardline())
                                    .append(translate_statement(&mutated_info.stmt, typ_dict)),
                            )),
                    }),
                false,
            )
        }
        Statement::ForLoop((x, _), (e1, _), (e2, _), (b, _)) => {
            let mutated_info = b.mutated.as_ref().unwrap().as_ref();
            let mut_tuple = make_tuple(mutated_info.vars.iter().map(|i| translate_ident(i)));
            let closure_tuple = make_tuple(vec![translate_ident(x), mut_tuple.clone()]);
            let loop_expr = RcDoc::as_string("foldi")
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1, typ_dict)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2, typ_dict)))
                .append(RcDoc::space())
                .append(RcDoc::as_string("(fun"))
                .append(RcDoc::space())
                .append(closure_tuple)
                .append(RcDoc::space())
                .append(RcDoc::as_string("->"))
                .append(RcDoc::line())
                .append(translate_block(b, true, typ_dict))
                .append(RcDoc::hardline())
                .append(translate_statement(&mutated_info.stmt, typ_dict))
                .append(RcDoc::as_string(")"))
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(mut_tuple.clone());
            make_let_binding(mut_tuple, None, loop_expr, false)
        }
    }
    .group()
}

fn translate_block<'a>(
    b: &'a Block,
    omit_extra_unit: bool,
    typ_dict: &'a TypeDict,
) -> RcDoc<'a, ()> {
    RcDoc::intersperse(
        b.stmts
            .iter()
            .map(|(i, _)| translate_statement(i, typ_dict).group()),
        RcDoc::hardline(),
    )
    .append(match (&b.return_typ, omit_extra_unit) {
        (None, _) => panic!(), // should not happen,
        (Some(((Borrowing::Consumed, _), (BaseTyp::Unit, _))), false) => {
            RcDoc::hardline().append(RcDoc::as_string("()"))
        }
        (Some(_), _) => RcDoc::nil(),
    })
}

fn translate_item<'a>(i: &'a Item, typ_dict: &'a TypeDict) -> RcDoc<'a, ()> {
    match i {
        Item::FnDecl((f, _), sig, (b, _)) => make_let_binding(
            translate_ident(f)
                .append(RcDoc::line())
                .append(if sig.args.len() > 0 {
                    RcDoc::intersperse(
                        sig.args.iter().map(|((x, _), (tau, _))| {
                            make_paren(
                                translate_ident(x)
                                    .append(RcDoc::space())
                                    .append(RcDoc::as_string(":"))
                                    .append(RcDoc::space())
                                    .append(translate_typ(tau)),
                            )
                        }),
                        RcDoc::line(),
                    )
                } else {
                    RcDoc::as_string("()")
                })
                .append(RcDoc::line())
                .append(
                    RcDoc::as_string(":")
                        .append(RcDoc::space())
                        .append(translate_base_typ(&sig.ret.0))
                        .group(),
                ),
            None,
            translate_block(b, false, typ_dict)
                .append(if let BaseTyp::Unit = sig.ret.0 {
                    RcDoc::hardline().append(RcDoc::as_string("()"))
                } else {
                    RcDoc::nil()
                })
                .group(),
            true,
        ),
        Item::ArrayDecl(name, size, cell_t) => RcDoc::as_string("type")
            .append(RcDoc::space())
            .append(translate_ident(&name.0))
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .group()
            .append(
                RcDoc::line()
                    .append(RcDoc::as_string(format!("{}.lseq", SEQ_MODULE)))
                    .append(RcDoc::space())
                    .append(translate_base_typ(&cell_t.0))
                    .append(RcDoc::space())
                    .append(translate_expression(&size.0, typ_dict))
                    .group()
                    .nest(2),
            ),
        Item::ConstDecl(name, ty, e) => make_let_binding(
            translate_ident(&name.0),
            Some(translate_base_typ(&ty.0)),
            translate_expression(&e.0, typ_dict),
            true,
        ),
        Item::NaturalIntegerDecl(_nat_name, canvas_name, _secrecy, canvas_size, _modulo) => {
            RcDoc::as_string("type")
                .append(RcDoc::space())
                .append(translate_ident(&canvas_name.0))
                .append(RcDoc::space())
                .append(RcDoc::as_string("="))
                .group()
                .append(
                    RcDoc::line()
                        .append(RcDoc::as_string("Seq.lseq"))
                        .append(RcDoc::space())
                        .append(translate_base_typ(&BaseTyp::UInt8))
                        .append(RcDoc::space())
                        .append(translate_expression(&canvas_size.0, typ_dict))
                        .group()
                        .nest(2),
                )
                .append(RcDoc::hardline())
                .append(RcDoc::hardline()) //TODO: add other decl
                .append(RcDoc::as_string("// missing natural mod int type decl!"))
        }
    }
}

fn translate_program<'a>(p: &'a Program, typ_dict: &'a TypeDict) -> RcDoc<'a, ()> {
    RcDoc::concat(p.items.iter().map(|(i, _)| {
        translate_item(i, typ_dict)
            .append(RcDoc::hardline())
            .append(RcDoc::hardline())
    }))
}

pub fn translate_and_write_to_file(sess: &Session, p: &Program, file: &str, typ_dict: &TypeDict) {
    let file = file.trim();
    let path = path::Path::new(file);
    let mut file = match File::create(&path) {
        Err(why) => {
            sess.err(format!("Unable to write to outuput file {}: \"{}\"", file, why).as_str());
            return;
        }
        Ok(file) => file,
    };
    let width = 80;
    let mut w = Vec::new();
    let module_name = path.file_stem().unwrap().to_str().unwrap();
    write!(
        file,
        "module {}\n\nopen Hacspec\nopen FStar.Mul\n\nmodule RSeq = Hacspec.Seq\n\n",
        module_name
    )
    .unwrap();
    translate_program(p, typ_dict)
        .render(width, &mut w)
        .unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
