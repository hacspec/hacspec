use crate::rustspec::*;
use pretty::RcDoc;
use rustc_ast::ast::BinOpKind;
use rustc_session::Session;
use rustc_span::symbol::Ident;
use std::fs::File;
use std::io::Write;
use std::path;

fn translate_ident(x: &Ident) -> RcDoc<()> {
    RcDoc::as_string(x.name.to_ident_string())
}

fn translate_path(p: &Path) -> RcDoc<()> {
    RcDoc::intersperse(
        p.location.iter().map(|x| translate_ident(x)),
        RcDoc::as_string("_"),
    )
    .append(match &p.arg {
        None => RcDoc::nil(),
        Some(arg) => RcDoc::space().append(translate_base_typ(&arg)),
    })
    .group()
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
        BaseTyp::Named(p) => translate_path(p),
        BaseTyp::Tuple(_) => panic!(),
    }
}

fn translate_typ((_, (tau, _)): &Typ) -> RcDoc<()> {
    translate_base_typ(tau)
}

fn translate_literal(lit: &Literal) -> RcDoc<()> {
    match lit {
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
        Pattern::IdentPat(x, _) => translate_ident(x),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => RcDoc::as_string("(")
            .append(RcDoc::intersperse(
                pats.iter().map(|(pat, _)| translate_pattern(pat)),
                RcDoc::as_string(",").append(RcDoc::space()),
            ))
            .append(RcDoc::as_string(")")),
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
        Expression::Tuple(es) => RcDoc::as_string("(")
            .append(RcDoc::intersperse(
                es.iter().map(|(e, _)| translate_expression(e)),
                RcDoc::as_string(",").append(RcDoc::space()),
            ))
            .append(RcDoc::as_string(")")),
        Expression::Named(p) => translate_path(p),
        Expression::FuncCall((f, _), args) => translate_path(f).append(if args.len() > 0 {
            RcDoc::concat(args.iter().map(|(arg, _)| {
                RcDoc::space()
                    .append(RcDoc::as_string("("))
                    .append(translate_expression(arg))
                    .append(RcDoc::as_string(")"))
            }))
        } else {
            RcDoc::space().append(RcDoc::as_string("()"))
        }),
        Expression::MethodCall(sel, (f, _), args) => translate_ident(f)
            .append(RcDoc::space())
            .append({
                let sel = &sel.0;
                translate_expression(sel)
            })
            .append(RcDoc::concat(args.iter().map(|(arg, _)| {
                RcDoc::space()
                    .append(RcDoc::as_string("("))
                    .append(translate_expression(arg))
                    .append(RcDoc::as_string(")"))
            }))),
        Expression::ArrayIndex(e1, e2) => {
            let e1 = &e1.0;
            let e2 = &e2.0;
            RcDoc::as_string("array_index")
                .append(RcDoc::space())
                .append(RcDoc::as_string("("))
                .append(translate_expression(e1))
                .append(RcDoc::as_string(")"))
                .append(RcDoc::space())
                .append(RcDoc::as_string("("))
                .append(translate_expression(e2))
                .append(RcDoc::as_string(")"))
        }
    }
}

fn translate_statement(s: &Statement) -> RcDoc<()> {
    match s {
        Statement::LetBinding((pat, _), typ, (expr, _)) => RcDoc::as_string("let")
            .append(RcDoc::space())
            .append(translate_pattern(pat))
            .append(match typ {
                None => RcDoc::nil(),
                Some((tau, _)) => RcDoc::space()
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(translate_typ(tau)),
            })
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .append(RcDoc::space())
            .append(translate_expression(expr).group())
            .append(RcDoc::space())
            .append(RcDoc::as_string("in")),
        Statement::Reassignment(x, (e1, _)) => RcDoc::as_string("let")
            .append(RcDoc::space())
            .append(translate_ident(x))
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .append(RcDoc::space())
            .append(translate_expression(e1))
            .append(RcDoc::space())
            .append(RcDoc::as_string("in")),
        Statement::ArrayUpdate(x, (e1, _), (e2, _)) => RcDoc::as_string("let")
            .append(RcDoc::space())
            .append(translate_ident(x))
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .append(RcDoc::space())
            .append(RcDoc::as_string("array_upd"))
            .append(RcDoc::space())
            .append(translate_ident(x))
            .append(RcDoc::space())
            .append(RcDoc::as_string("("))
            .append(translate_expression(e1))
            .append(RcDoc::as_string(")"))
            .append(RcDoc::space())
            .append(RcDoc::as_string("("))
            .append(translate_expression(e2))
            .append(RcDoc::as_string(")"))
            .append(RcDoc::space())
            .append(RcDoc::as_string("in")),
        Statement::ReturnExp(e1) => translate_expression(e1),
        Statement::Conditional((cond, _), (b1, _), b2) => RcDoc::as_string("if")
            .append(RcDoc::space())
            .append(translate_expression(cond))
            .append(RcDoc::space())
            .append(RcDoc::as_string("then"))
            .append(RcDoc::space())
            .append(RcDoc::as_string("begin"))
            .append(RcDoc::line())
            .group()
            .append(translate_block(b1))
            .group()
            .nest(2)
            .append(RcDoc::line())
            .append(RcDoc::as_string("end"))
            .append(match b2 {
                None => RcDoc::nil(),
                Some((b2, _)) => RcDoc::space()
                    .append(RcDoc::as_string("else"))
                    .append(RcDoc::as_string("begin"))
                    .append(RcDoc::line())
                    .append(translate_block(b2))
                    .group()
                    .nest(2)
                    .append(RcDoc::line())
                    .append(RcDoc::as_string("end")),
            })
            .append(RcDoc::as_string(";")),
        Statement::ForLoop(_, _, _, _) => unimplemented!(),
    }
    .group()
}

fn translate_block(b: &Block) -> RcDoc<()> {
    RcDoc::intersperse(
        b.iter().map(|(i, _)| translate_statement(i).group()),
        RcDoc::hardline(),
    )
}

fn translate_item(i: &Item) -> RcDoc<()> {
    match i {
        Item::FnDecl(f, sig, (b, _)) => RcDoc::as_string("let")
            .append(RcDoc::space())
            .append(translate_ident(f))
            .append(RcDoc::line())
            .append(if sig.args.len() > 0 {
                RcDoc::intersperse(
                    sig.args.iter().map(|((x, _), (tau, _))| {
                        RcDoc::as_string("(")
                            .append(translate_ident(x))
                            .append(RcDoc::space())
                            .append(RcDoc::as_string(":"))
                            .append(RcDoc::space())
                            .append(translate_typ(tau))
                            .append(RcDoc::as_string(")"))
                            .group()
                    }),
                    RcDoc::line(),
                )
            } else {
                RcDoc::as_string("()")
            })
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .group()
            .append(RcDoc::line())
            .append(translate_block(b))
            .append(if let BaseTyp::Unit = sig.ret.0 {
                RcDoc::hardline().append(RcDoc::as_string("()"))
            } else {
                RcDoc::nil()
            })
            .nest(2)
            .group(),
    }
}

fn translate_program(p: &Program) -> RcDoc<()> {
    RcDoc::concat(p.iter().map(|(i, _)| {
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
