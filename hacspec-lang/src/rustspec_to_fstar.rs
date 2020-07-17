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

fn translate_literal(p: &Literal) -> RcDoc<()> {
    RcDoc::nil()
}

fn translate_pattern(p: &Pattern) -> RcDoc<()> {
    match p {
        Pattern::IdentPat(x, _) => translate_ident(x),
        _ => RcDoc::nil(),
    }
}

fn translate_binop(op: &BinOpKind) -> RcDoc<()> {
    match op {
        BinOpKind::Sub => RcDoc::as_string("-"),
        _ => RcDoc::nil(),
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
                .group()
                .append(RcDoc::space())
                .append(translate_expression(e2))
        }
        Expression::Named(p) => translate_path(p),
        _ => RcDoc::nil(),
    }
}

fn translate_statement(s: &Statement) -> RcDoc<()> {
    match s {
        Statement::LetBinding((pat, _), typ, (expr, _)) => translate_pattern(pat)
            .append(match typ {
                None => RcDoc::nil(),
                Some((tau, _)) => RcDoc::space()
                    .append(RcDoc::as_string(":"))
                    .append(RcDoc::space())
                    .append(translate_typ(tau)),
            })
            .append(RcDoc::space())
            .append(RcDoc::as_string("="))
            .group()
            .append(RcDoc::space())
            .append(translate_expression(expr))
            .group(),
        _ => RcDoc::nil(),
    }
}

fn translate_block(b: &Block) -> RcDoc<()> {
    RcDoc::intersperse(
        b.iter().map(|(i, _)| {
            RcDoc::as_string("let")
                .append(RcDoc::space())
                .append(translate_statement(i))
                .append(RcDoc::space())
                .append(RcDoc::as_string("in"))
        }),
        RcDoc::line(),
    )
    .group()
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
            .append(RcDoc::hardline())
            .nest(2)
            .append(translate_block(b)),
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
