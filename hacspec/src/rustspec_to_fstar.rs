use crate::rustspec::*;

use core::iter::IntoIterator;
use pretty::RcDoc;
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;
use std::fs::File;
use std::io::Write;
use std::path;

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
    RcDoc::as_string(format!("{}", x))
}

fn translate_base_typ(tau: &BaseTyp) -> RcDoc<()> {
    match tau {
        BaseTyp::Unit => RcDoc::as_string("unit"),
        BaseTyp::Bool => RcDoc::as_string("bool"),
        BaseTyp::UInt8 => RcDoc::as_string("UInt8.t"),
        BaseTyp::Int8 => RcDoc::as_string("Int8.t"),
        BaseTyp::UInt16 => RcDoc::as_string("UInt16.t"),
        BaseTyp::Int16 => RcDoc::as_string("Int16.t"),
        BaseTyp::UInt32 => RcDoc::as_string("UInt32.t"),
        BaseTyp::Int32 => RcDoc::as_string("Int32.t"),
        BaseTyp::UInt64 => RcDoc::as_string("UInt64.t"),
        BaseTyp::Int64 => RcDoc::as_string("Int64.t"),
        BaseTyp::UInt128 => RcDoc::as_string("UInt128.t"),
        BaseTyp::Int128 => RcDoc::as_string("Int128.t"),
        BaseTyp::Usize => RcDoc::as_string("UInt32.t"),
        BaseTyp::Isize => RcDoc::as_string("Int32.t"),
        BaseTyp::Seq(tau) => {
            let tau: &BaseTyp = &tau.0;
            RcDoc::as_string("Seq.seq")
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .group()
        }
        BaseTyp::Array(size, tau) => {
            let tau: &BaseTyp = &tau.0;
            RcDoc::as_string("Seq.lseq")
                .append(RcDoc::space())
                .append(translate_base_typ(tau))
                .append(RcDoc::space())
                .append(RcDoc::as_string(match &size.0 {
                    ArraySize::Ident(id) => format!("{}", id),
                    ArraySize::Integer(i) => format!("{}", i),
                }))
                .group()
        }
        BaseTyp::Named(ident, arg) => translate_ident(&ident.0).append(match arg {
            None => RcDoc::nil(),
            Some(arg) => RcDoc::space().append(translate_base_typ(&arg.as_ref().0)),
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

fn translate_func_name<'a>(prefix: &'a Option<Spanned<BaseTyp>>, name: &'a Ident) -> RcDoc<'a, ()> {
    match prefix {
        None => translate_ident(name),
        Some((prefix, _)) => {
            let module_name = match prefix {
                BaseTyp::Bool => panic!(), // should not happen
                BaseTyp::Unit => panic!(), // should not happen
                BaseTyp::UInt8 => RcDoc::as_string("UInt8"),
                BaseTyp::Int8 => RcDoc::as_string("Int8"),
                BaseTyp::UInt16 => RcDoc::as_string("UInt16"),
                BaseTyp::Int16 => RcDoc::as_string("Int16"),
                BaseTyp::UInt32 => RcDoc::as_string("UInt32"),
                BaseTyp::Int32 => RcDoc::as_string("Int32"),
                BaseTyp::UInt64 => RcDoc::as_string("UInt64"),
                BaseTyp::Int64 => RcDoc::as_string("Int64"),
                BaseTyp::UInt128 => RcDoc::as_string("UInt128"),
                BaseTyp::Int128 => RcDoc::as_string("Int128"),
                BaseTyp::Usize => RcDoc::as_string("UInt32"),
                BaseTyp::Isize => RcDoc::as_string("Int32"),
                BaseTyp::Seq(_) | BaseTyp::Array(_, _) => RcDoc::as_string("Seq"),
                BaseTyp::Named(ident, _) => translate_ident(&ident.0),
                BaseTyp::Variable(_) => panic!(), // shoult not happen
                BaseTyp::Tuple(_) => panic!(),    // should not happen
                BaseTyp::NaturalInteger(_, _) => unimplemented!(),
            };
            let type_arg = match prefix {
                BaseTyp::Seq(tau) => Some(translate_base_typ(&tau.0)),
                BaseTyp::Array(_, tau) => Some(translate_base_typ(&tau.0)),
                _ => None,
            };
            module_name
                .append(RcDoc::as_string("."))
                .append(translate_ident(name))
                .append(match type_arg {
                    None => RcDoc::nil(),
                    Some(arg) => RcDoc::space().append(RcDoc::as_string("#")).append(arg),
                })
        }
    }
}

fn translate_expression(e: &Expression) -> RcDoc<()> {
    match e {
        Expression::Binary((op, _), ref e1, ref e2) => {
            let e1 = &e1.0;
            let e2 = &e2.0;
            translate_expression(e1)
                .append(RcDoc::space())
                .append(translate_binop(op))
                .append(RcDoc::space())
                .append(translate_expression(e2))
                .group()
        }
        Expression::Unary(op, e1) => {
            let e1 = &e1.0;
            translate_unop(op)
                .append(RcDoc::space())
                .append(translate_expression(e1))
                .group()
        }
        Expression::Lit(lit) => translate_literal(lit),
        Expression::Tuple(es) => make_tuple(es.into_iter().map(|(e, _)| translate_expression(&e))),
        Expression::Named(p) => translate_ident(p),
        Expression::FuncCall(prefix, name, args) => {
            translate_func_name(prefix, &name.0).append(if args.len() > 0 {
                RcDoc::concat(args.iter().map(|((arg, _), _)| {
                    RcDoc::space().append(make_paren(translate_expression(arg)))
                }))
            } else {
                RcDoc::space().append(RcDoc::as_string("()"))
            })
        }
        Expression::MethodCall(_, _, (f, _), args) => translate_ident(f)
            .append(RcDoc::concat(args.iter().map(|((arg, _), _)| {
                RcDoc::space().append(make_paren(translate_expression(arg)))
            }))),
        Expression::ArrayIndex(x, e2) => {
            let e2 = &e2.0;
            RcDoc::as_string("array_index")
                .append(RcDoc::space())
                .append(make_paren(translate_ident(&x.0)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2)))
        }
        Expression::NewArray(_, _, _) => panic!(),
        Expression::IntegerCasting(_, _) => panic!(),
    }
}

fn translate_statement(s: &Statement) -> RcDoc<()> {
    match s {
        Statement::LetBinding((pat, _), typ, (expr, _)) => make_let_binding(
            translate_pattern(pat),
            typ.as_ref().map(|(typ, _)| translate_typ(typ)),
            translate_expression(expr),
            false,
        ),
        Statement::Reassignment((x, _), (e1, _)) => {
            make_let_binding(translate_ident(x), None, translate_expression(e1), false)
        }
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _)) => make_let_binding(
            translate_ident(x),
            None,
            RcDoc::as_string("array_upd")
                .append(RcDoc::space())
                .append(translate_ident(x))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2))),
            false,
        ),
        Statement::ReturnExp(e1) => translate_expression(e1),
        Statement::Conditional((cond, _), (b1, _), b2, mutated) => {
            let mutated_info = mutated.as_ref().unwrap().as_ref();
            make_let_binding(
                make_tuple(mutated_info.vars.iter().map(|i| translate_ident(i))),
                None,
                RcDoc::as_string("if")
                    .append(RcDoc::space())
                    .append(translate_expression(cond))
                    .append(RcDoc::space())
                    .append(RcDoc::as_string("then"))
                    .append(RcDoc::space())
                    .append(make_begin_paren(
                        translate_block(b1, true)
                            .append(RcDoc::hardline())
                            .append(translate_statement(&mutated_info.stmt)),
                    ))
                    .append(match b2 {
                        None => RcDoc::space()
                            .append(RcDoc::as_string("else"))
                            .append(RcDoc::space())
                            .append(make_begin_paren(translate_statement(&mutated_info.stmt))),
                        Some((b2, _)) => RcDoc::space()
                            .append(RcDoc::as_string("else"))
                            .append(RcDoc::space())
                            .append(make_begin_paren(
                                translate_block(b2, true)
                                    .append(RcDoc::hardline())
                                    .append(translate_statement(&mutated_info.stmt)),
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
                .append(make_paren(translate_expression(e1)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2)))
                .append(RcDoc::space())
                .append(RcDoc::as_string("(fun"))
                .append(RcDoc::space())
                .append(closure_tuple)
                .append(RcDoc::space())
                .append(RcDoc::as_string("->"))
                .append(RcDoc::line())
                .append(translate_block(b, true))
                .append(RcDoc::hardline())
                .append(translate_statement(&mutated_info.stmt))
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

fn translate_block(b: &Block, omit_extra_unit: bool) -> RcDoc<()> {
    RcDoc::intersperse(
        b.stmts.iter().map(|(i, _)| translate_statement(i).group()),
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

fn translate_item(i: &Item) -> RcDoc<()> {
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
            translate_block(b, false)
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
                    .append(RcDoc::as_string("Seq.lseq"))
                    .append(RcDoc::space())
                    .append(translate_base_typ(&cell_t.0))
                    .append(RcDoc::space())
                    .append(translate_expression(&size.0))
                    .group()
                    .nest(2),
            ),
        Item::ConstDecl(_, _, _) => unimplemented!(),
        Item::NaturalIntegerDecl(_, _, _, _, _) => unimplemented!(),
    }
}

fn translate_program(p: &Program) -> RcDoc<()> {
    RcDoc::concat(p.items.iter().map(|(i, _)| {
        translate_item(i)
            .append(RcDoc::hardline())
            .append(RcDoc::hardline())
    }))
}

pub fn translate_and_write_to_file(sess: &Session, p: &Program, file: &str) {
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
    translate_program(p).render(width, &mut w).unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
