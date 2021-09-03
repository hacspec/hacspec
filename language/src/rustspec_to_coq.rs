use crate::name_resolution::{DictEntry, TopLevelContext};
use crate::rustspec::*;
use core::iter::IntoIterator;
use core::slice::Iter;
use heck::{SnakeCase, TitleCase};
use itertools::Itertools;
use lazy_static::lazy_static;
use pretty::RcDoc;
use regex::Regex;
use rustc_session::Session;
use rustc_span::DUMMY_SP;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

const SEQ_MODULE: &'static str = "seq";

const ARRAY_MODULE: &'static str = "array";

const NAT_MODULE: &'static str = "nat_mod";

static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_codegen_id() -> usize {
    ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

lazy_static! {
    static ref ID_MAP: Mutex<HashMap<usize, usize>> = Mutex::new(HashMap::new());
}

fn make_let_binding<'a>(
    pat: RcDoc<'a, ()>,
    typ: Option<RcDoc<'a, ()>>,
    expr: RcDoc<'a, ()>,
    toplevel: bool,
) -> RcDoc<'a, ()> {
    RcDoc::as_string(if toplevel { "Definition" } else { "let" })
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
            .append(RcDoc::as_string("×"))
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
    RcDoc::as_string("(")
    .append(RcDoc::line().append(e).group().nest(2))
    .append(RcDoc::line())
    .append(RcDoc::as_string(")"))
}

fn translate_toplevel_ident<'a>(x: TopLevelIdent) -> RcDoc<'a, ()> {
    translate_ident_str(x.0)
}

fn translate_ident<'a>(x: Ident) -> RcDoc<'a, ()> {
    match x {
        Ident::Unresolved(s) => translate_ident_str(s.clone()),
        Ident::TopLevel(s) => translate_toplevel_ident(s),
        Ident::Local(LocalIdent { id, name: s }) => {
            let mut id_map = ID_MAP.lock().unwrap();
            let codegen_id: usize = match id_map.get(&id) {
                Some(c_id) => *c_id,
                None => {
                    let c_id = fresh_codegen_id();
                    id_map.insert(id, c_id);
                    c_id
                }
            };
            translate_ident_str(format!("{}_{}", s, codegen_id))
        }
    }
}

fn translate_constructor<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    RcDoc::as_string(enum_name.0)
}

fn translate_enum_name<'a>(enum_name: TopLevelIdent) -> RcDoc<'a> {
    translate_toplevel_ident(enum_name)
}

fn translate_enum_case_name<'a>(enum_name: BaseTyp, case_name: TopLevelIdent) -> RcDoc<'a> {
    translate_constructor(case_name).append(match enum_name {
        BaseTyp::Named(name, _) => {
            if (name.0).0 == "Option" || (name.0).0 == "Result" {
                RcDoc::nil()
            } else {
                RcDoc::as_string("(")
                .append(translate_toplevel_ident(name.0))
                .append(RcDoc::as_string(")"))
            }
        }
        _ => panic!("should not happen"),
    })
}

fn translate_ident_str<'a>(ident_str: String) -> RcDoc<'a, ()> {
    let mut ident_str = ident_str.clone();
    let secret_int_regex = Regex::new(r"(?P<prefix>(U|I))(?P<digits>\d{1,3})").unwrap();
    ident_str = secret_int_regex
    .replace_all(&ident_str, r"${prefix}int${digits}")
    .to_string();
    let secret_signed_int_fix = Regex::new(r"iint").unwrap();
    ident_str = secret_signed_int_fix
    .replace_all(&ident_str, "int")
    .to_string();
    let mut snake_case_ident = ident_str.to_snake_case();
    if snake_case_ident == "new" {
        snake_case_ident = "new_".to_string();
    }
    RcDoc::as_string(snake_case_ident)
}

fn translate_base_typ<'a>(tau: BaseTyp) -> RcDoc<'a, ()> {
    match tau {
        BaseTyp::Unit => RcDoc::as_string("unit"),
        BaseTyp::Bool => RcDoc::as_string("bool"),
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
            make_typ_tuple(args.into_iter().map(|(arg, _)| translate_base_typ(arg)))
        }
        BaseTyp::NaturalInteger(_secrecy, modulo, _bits) => RcDoc::as_string("nat_mod")
        .append(RcDoc::space())
        .append(RcDoc::as_string(format!("0x{}", &modulo.0))),
    }
}

fn translate_typ<'a>((_, (tau, _)): Typ) -> RcDoc<'a, ()> {
    translate_base_typ(tau)
}

fn translate_literal<'a>(lit: Literal) -> RcDoc<'a, ()> {
    match lit {
        Literal::Unit => RcDoc::as_string("()"),
        Literal::Bool(true) => RcDoc::as_string("true"),
        Literal::Bool(false) => RcDoc::as_string("false"),
        Literal::Int128(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::UInt128(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::Int64(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::UInt64(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::Int32(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::UInt32(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::Int16(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::UInt16(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::Int8(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::UInt8(x) => RcDoc::as_string(format!("repr {}", x)),
        Literal::Isize(x) => RcDoc::as_string(format!("isize {}", x)),
        Literal::Usize(x) => RcDoc::as_string(format!("usize {}", x)),
        Literal::Str(msg) => RcDoc::as_string(format!("\"{}\"", msg)),
    }
}

fn get_type_default(t: &BaseTyp) -> Expression {
    match t {
        BaseTyp::UInt8 => Expression::Lit(Literal::UInt8(0)),
        BaseTyp::Int8 => Expression::Lit(Literal::Int8(0)),
        BaseTyp::UInt16 => Expression::Lit(Literal::UInt16(0)),
        BaseTyp::Int16 => Expression::Lit(Literal::Int16(0)),
        BaseTyp::UInt32 => Expression::Lit(Literal::UInt32(0)),
        BaseTyp::Int32 => Expression::Lit(Literal::Int32(0)),
        BaseTyp::UInt64 => Expression::Lit(Literal::UInt64(0)),
        BaseTyp::Int64 => Expression::Lit(Literal::Int64(0)),
        BaseTyp::UInt128 => Expression::Lit(Literal::UInt128(0)),
        BaseTyp::Int128 => Expression::Lit(Literal::Int128(0)),
        BaseTyp::Usize => Expression::Lit(Literal::Usize(0)),
        BaseTyp::Isize => Expression::Lit(Literal::Isize(0)),
        BaseTyp::Named((name, i_s), None) => match name.0.as_str() {
            "U8" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::UInt8(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "I8" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::Int8(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "U16" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::UInt16(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "I16" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::Int16(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "U32" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::UInt32(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "I32" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::Int32(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "U64" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::UInt64(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "I64" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::Int64(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "U128" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::UInt128(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            "I128" => Expression::FuncCall(
                None,
                (name.clone(), i_s.clone()),
                vec![(
                    (Expression::Lit(Literal::Int128(0)), i_s.clone()),
                    (Borrowing::Consumed, i_s.clone()),
                )],
            ),
            _ => panic!("Trying to get default for {}", t),
        },
        _ => panic!("Trying to get default for {}", t),
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
            translate_enum_case_name(BaseTyp::Named(name.clone(), None), name.0.clone())
                .append(RcDoc::space())
                .append(make_paren(translate_pattern(inner_pat.0)))
        }
        Pattern::IdentPat(x) => translate_ident(x.clone()),
        Pattern::WildCard => RcDoc::as_string("_"),
        Pattern::Tuple(pats) => make_tuple(pats.into_iter().map(|(pat, _)| translate_pattern(pat))),
    }
}

fn translate_binop<'a, 'b>(
    op: BinOpKind,
    op_typ: &'b Typ,
    top_ctx: &'a TopLevelContext,
) -> RcDoc<'a, ()> {
    match (op, &(op_typ.1).0) {
        (_, BaseTyp::Named(ident, _)) => {
            let ident = &ident.0;
            match top_ctx.typ_dict.get(ident) {
                Some((inner_ty, entry)) => match entry {
                    DictEntry::NaturalInteger => match op {
                        BinOpKind::Sub => return RcDoc::as_string("-%"),
                        BinOpKind::Add => return RcDoc::as_string("+%"),
                        BinOpKind::Mul => return RcDoc::as_string("*%"),
                        BinOpKind::Div => return RcDoc::as_string("/%"),
                        BinOpKind::BitXor => return RcDoc::as_string("xor"),
                        BinOpKind::BitOr => return RcDoc::as_string("or"),
                        BinOpKind::BitAnd => return RcDoc::as_string("and"),
                        BinOpKind::Eq => return RcDoc::as_string("=.?"),
                        BinOpKind::Ne => return RcDoc::as_string("!=.?"),
                        _ => unimplemented!(),
                    },
                    DictEntry::Enum | DictEntry::Array | DictEntry::Alias => {
                        return translate_binop(op, inner_ty, top_ctx)
                    }
                },
                _ => (), // should not happen
            }
        }
        _ => (),
    };
    match (op, &(op_typ.1).0) {
        (_, BaseTyp::Seq(inner_ty)) | (_, BaseTyp::Array(_, inner_ty)) => {
            let _inner_ty_op = translate_binop(
                op,
                &(
                    (Borrowing::Consumed, inner_ty.1.clone()),
                    inner_ty.as_ref().clone(),
                ),
                top_ctx,
            );
            let op_str = match op {
                BinOpKind::Sub => "minus",
                BinOpKind::Add => "add",
                BinOpKind::Mul => "mul",
                BinOpKind::Div => "div",
                BinOpKind::BitXor => "xor",
                BinOpKind::BitOr => "or",
                BinOpKind::BitAnd => "and",
                BinOpKind::Eq => "eq",
                BinOpKind::Ne => "neq",
                _ => panic!("operator: {:?}", op), // should not happen
            };
            RcDoc::as_string(format!(
                "{}_{}",
                match &(op_typ.1).0 {
                    BaseTyp::Seq(_) => SEQ_MODULE,
                    BaseTyp::Array(_, _) => ARRAY_MODULE,
                    _ => panic!(), // should not happen
                },
                op_str
            ))
        }
        (BinOpKind::Sub, BaseTyp::Usize) | (BinOpKind::Sub, BaseTyp::Isize) => {
            RcDoc::as_string("-")
        }
        (BinOpKind::Add, BaseTyp::Usize) | (BinOpKind::Add, BaseTyp::Isize) => {
            RcDoc::as_string("+")
        }
        (BinOpKind::Mul, BaseTyp::Usize) | (BinOpKind::Mul, BaseTyp::Isize) => {
            RcDoc::as_string("*")
        }
        (BinOpKind::Div, BaseTyp::Usize) | (BinOpKind::Div, BaseTyp::Isize) => {
            RcDoc::as_string("/")
        }
        (BinOpKind::Rem, BaseTyp::Usize) | (BinOpKind::Rem, BaseTyp::Isize) => {
            RcDoc::as_string("%%")
        }
        (BinOpKind::Shl, BaseTyp::Usize) => RcDoc::as_string("usize_shift_left"),
        (BinOpKind::Shr, BaseTyp::Usize) => RcDoc::as_string("usize_shift_right"),
        (BinOpKind::Rem, _) => RcDoc::as_string(".%"),
        (BinOpKind::Sub, _) => RcDoc::as_string(".-"),
        (BinOpKind::Add, _) => RcDoc::as_string(".+"),
        (BinOpKind::Mul, _) => RcDoc::as_string(".*"),
        (BinOpKind::Div, _) => RcDoc::as_string("./"),
        (BinOpKind::BitXor, _) => RcDoc::as_string(".^"),
        (BinOpKind::BitAnd, _) => RcDoc::as_string(".&"),
        (BinOpKind::BitOr, _) => RcDoc::as_string(".|"),
        (BinOpKind::Shl, _) => RcDoc::as_string("shift_left"),
        (BinOpKind::Shr, _) => RcDoc::as_string("shift_right"),
        (BinOpKind::Lt, _) => RcDoc::as_string("<.?"),
        (BinOpKind::Le, _) => RcDoc::as_string("<=.?"),
        (BinOpKind::Ge, _) => RcDoc::as_string(">=.?"),
        (BinOpKind::Gt, _) => RcDoc::as_string(">.?"),
        (BinOpKind::Ne, _) => RcDoc::as_string("!=.?"),
        (BinOpKind::Eq, _) => RcDoc::as_string("=.?"),
        (BinOpKind::And, _) => RcDoc::as_string("&&"),
        (BinOpKind::Or, _) => RcDoc::as_string("||"),
    }
}

fn translate_unop<'a>(op: UnOpKind, _op_typ: Typ) -> RcDoc<'a, ()> {
    match (op, &(_op_typ.1).0) {
        (UnOpKind::Not, BaseTyp::Bool) => RcDoc::as_string("negb"),
        (UnOpKind::Not, _) => RcDoc::as_string("not"),
        (UnOpKind::Neg, _) => RcDoc::as_string("-"),
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
                _ => (translate_ident_str(name.0.clone()), FuncPrefix::Regular),
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
) -> (RcDoc<'a, ()>, Vec<RcDoc<'a, ()>>) {
    match prefix.clone() {
        None => {
            let name = translate_ident(name.clone());
            match format!("{}", name.pretty(0)).as_str() {
                "uint128" | "uint64" | "uint32" | "uint16" | "uint8" | "int128" | "int64"
                | "int32" | "int16" | "int8" => {
                    // In this case, we're trying to apply a secret
                    // int constructor. The value it is applied to is
                    // a public integer of the same kind. So in Coq, that
                    // will amount to a classification operation
                    // TODO: may need to add type annotation here
                    (RcDoc::as_string("secret"), vec![])
                }
                _ => (name, vec![]),
            }
        }
        Some((prefix, _)) => {
            let (module_name, prefix_info) =
            translate_prefix_for_func_name(prefix.clone(), top_ctx);
            let func_ident = translate_ident(name.clone());
            let mut additional_args = Vec::new();
            // We add the modulo value for nat_mod
            match (
                format!("{}", module_name.pretty(0)).as_str(),
                format!("{}", func_ident.pretty(0)).as_str(),
            ) {
                (NAT_MODULE, "from_literal") | (NAT_MODULE, "pow2") => {
                    match &prefix_info {
                        FuncPrefix::NatMod(modulo, _bits) => {
                            additional_args.push(RcDoc::as_string(format!("0x{}", modulo)));
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
                        FuncPrefix::Array(_, inner_ty) | FuncPrefix::Seq(inner_ty) => {
                            additional_args
                            .push(translate_expression(get_type_default(inner_ty), top_ctx))
                        }
                        _ => panic!(), // should not happen
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
                            additional_args.push(translate_ident_str(s.0.clone()))
                        }
                        FuncPrefix::Array(ArraySize::Integer(i), _) => {
                            additional_args.push(RcDoc::as_string(format!("{}", i)))
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
            )
        }
    }
}

fn translate_expression<'a>(e: Expression, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match e {
        Expression::Binary((op, _), e1, e2, op_typ) => {
            let e1 = e1.0;
            let e2 = e2.0;
            make_paren(translate_expression(e1, top_ctx))
            .append(RcDoc::space())
            .append(translate_binop(op, op_typ.as_ref().unwrap(), top_ctx))
            .append(RcDoc::space())
            .append(make_paren(translate_expression(e2, top_ctx)))
            .group()
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
        .append(RcDoc::as_string("end")),
        //todo
        Expression::EnumInject(enum_name, case_name, payload) => {
            translate_enum_case_name(enum_name.clone(), case_name.0.clone()).append(match payload {
                None => RcDoc::nil(),
                Some(payload) => RcDoc::space().append(make_paren(translate_expression(
                    *payload.0.clone(),
                    top_ctx,
                ))),
            })
        }
        Expression::InlineConditional(cond, e_t, e_f) => {
            let cond = cond.0;
            let e_t = e_t.0;
            let e_f = e_f.0;
            RcDoc::as_string("if")
            .append(RcDoc::space())
            .append(make_paren(translate_expression(cond, top_ctx)))
            .append(RcDoc::as_string(":bool"))
            .append(RcDoc::space())
            .append(RcDoc::as_string("then"))
            .append(RcDoc::space())
            .append(make_paren(translate_expression(e_t, top_ctx)))
            .append(RcDoc::space())
            .append(RcDoc::as_string("else"))
            .append(RcDoc::space())
            .append(make_paren(translate_expression(e_f, top_ctx)))
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
        Expression::Tuple(es) => make_tuple(
            es.into_iter()
            .map(|(e, _)| translate_expression(e, top_ctx)),
        ),
        Expression::Named(p) => translate_ident(p.clone()),
        Expression::FuncCall(prefix, name, args) => {
            let (func_name, additional_args) =
            translate_func_name(prefix.clone(), Ident::TopLevel(name.0.clone()), top_ctx);
            let total_args = args.len() + additional_args.len();
            func_name
            // We append implicit arguments first
            .append(RcDoc::concat(
                additional_args
                .into_iter()
                .map(|arg| RcDoc::space().append(make_paren(arg))),
            ))
            // Then the explicit arguments
            .append(RcDoc::concat(args.into_iter().map(|((arg, _), _)| {
                RcDoc::space().append(make_paren(translate_expression(arg, top_ctx)))
            })))
            .append(if total_args == 0 {
                RcDoc::space()//.append(RcDoc::as_string("()"))
            } else {
                RcDoc::nil()
            })
        }
        Expression::MethodCall(sel_arg, sel_typ, (f, _), args) => {
            let (func_name, additional_args) =
            translate_func_name(sel_typ.clone().map(|x| x.1), Ident::TopLevel(f), top_ctx);
            func_name // We append implicit arguments first
            .append(RcDoc::concat(
                additional_args
                .into_iter()
                .map(|arg| RcDoc::space().append(make_paren(arg))),
            ))
            // Then the self argument
            .append(
                RcDoc::space().append(make_paren(translate_expression((sel_arg.0).0, top_ctx))),
            )
            // And finally the rest of the arguments
            .append(RcDoc::concat(args.into_iter().map(|((arg, _), _)| {
                RcDoc::space().append(make_paren(translate_expression(arg, top_ctx)))
            })))
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
        Expression::NewArray(_, typ, args) => {
            // retrieves the element type of the array. For named types (aliases), it looks up
            // the original definition in the typ_dict.
            let inner_ty = match typ {
                Some(BaseTyp::Named(ident, _)) => {
                    let ident = &ident.0;
                    match top_ctx.typ_dict.get(ident) {
                        Some((alias_typ, DictEntry::Array)) => {
                            match (alias_typ.1).0.clone() {
                                BaseTyp::Array(_size, inner_ty) => {
                                    inner_ty.as_ref().clone().0
                                }
                                _ => panic!(),           
                            }
                            // translate_prefix_for_func_name((alias_typ.1).0.clone(), top_ctx)
                        }
                        _ => panic!(),
                    }
                }
                Some(BaseTyp::Array(_size, inner_ty)) => {
                    inner_ty.as_ref().clone().0
                }
                // Should not happen - array should always have an element type
                _ => panic!(),
            };
            RcDoc::as_string(format!("{}_from_list", ARRAY_MODULE))
            .append(RcDoc::space())
            .append(translate_base_typ(inner_ty.clone()))
            .append(RcDoc::space())
            .append(make_paren(
                make_let_binding(
                    RcDoc::as_string("l"),
                    None,
                    make_list(
                        args.into_iter()
                        .map(|(e, _)| translate_expression(e, top_ctx)),
                    ),
                    false,
                )
                .append(RcDoc::space())
                .append(RcDoc::as_string("l")),
            ))
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
                        BaseTyp::Named((TopLevelIdent(s), _), None) => s.clone(),
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

// taken from rustspec_to_fstar
fn add_ok_if_result(stmt: Statement, question_mark: bool) -> Spanned<Statement> {
    (
        if question_mark {
            // If b has an early return, then we must prefix the returned
            // mutated variables by Ok
            match stmt {
                Statement::ReturnExp(e) => Statement::ReturnExp(Expression::EnumInject(
                    BaseTyp::Named((TopLevelIdent("Result".to_string()), DUMMY_SP.into()), None),
                    (TopLevelIdent("Ok".to_string()), DUMMY_SP.into()),
                    Some((Box::new(e.clone()), DUMMY_SP.into())),
                )),
                _ => panic!("should not happen"),
            }
        } else {
            stmt.clone()
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
            //TODO: not yet handled
            if question_mark {
                unimplemented!()
            } else {
                make_let_binding(
                    translate_pattern_tick(pat.clone()),
                    typ.map(|(typ, _)| translate_typ(typ)),
                    translate_expression(expr.clone(), top_ctx),
                    false,
                )
                .append(RcDoc::hardline())
                .append(translate_statements(statements, top_ctx))
            }
        }
        Statement::Reassignment((x, _), (e1, _), question_mark) => 
        //TODO: not yet handled
        if question_mark {
            unimplemented!()
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
        Statement::ArrayUpdate((x, _), (e1, _), (e2, _), question_mark, typ) => {
            let array_or_seq = array_or_seq(typ.unwrap(), top_ctx);
            let array_upd_payload = array_or_seq
                .append(RcDoc::as_string("_upd"))
                .append(RcDoc::space())
                .append(translate_ident(x.clone()))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2.clone(), top_ctx)));
            if question_mark {
                unimplemented!()
            } else {
                make_let_binding(translate_ident(x.clone()), None, array_upd_payload, false)
                    .append(RcDoc::hardline())
                    .append(translate_statements(statements, top_ctx))
            }
        }

        Statement::ReturnExp(e1) => translate_expression(e1.clone(), top_ctx),
        Statement::Conditional((cond, _), (mut b1, _), b2, mutated) => {
            let mutated_info = mutated.unwrap();
            let pat = RcDoc::as_string("'")
                    .append(
                        make_tuple(
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
                b1_question_mark,
            ));
            let expr = RcDoc::as_string("if")
                .append(RcDoc::space())
                .append(translate_expression(cond.clone(), top_ctx))
                .append(RcDoc::as_string(":bool"))
                .append(RcDoc::space())
                .append(RcDoc::as_string("then"))
                .append(RcDoc::space())
                .append(make_begin_paren(translate_block(b1, true, top_ctx)))
                .append(match b2 {
                    None => RcDoc::space()
                        .append(RcDoc::as_string("else"))
                        .append(RcDoc::space())
                        .append(make_begin_paren(translate_statements(
                            [(mutated_info.stmt.clone(), DUMMY_SP.into())].iter(),
                            top_ctx,
                        ))),
                    Some((mut b2, _)) => {
                        b2.stmts.push(add_ok_if_result(
                            mutated_info.stmt.clone(),
                            b2_question_mark,
                        ));
                        RcDoc::space()
                            .append(RcDoc::as_string("else"))
                            .append(RcDoc::space())
                            .append(make_begin_paren(translate_block(b2, true, top_ctx)))
                    }
                });
            if either_blocks_contains_question_mark {
                // TODO
                unimplemented!()
                // make_error_returning_let_binding(pat, None, expr, || {
                    // translate_statements(statements, top_ctx)
                // })
            } else {
                make_let_binding(pat, None, expr, false)
                    .append(RcDoc::hardline())
                    .append(translate_statements(statements, top_ctx))
            }
        }
        Statement::ForLoop((x, _), (e1, _), (e2, _), (mut b, _)) => {
            let mutated_info = b.mutated.clone().unwrap();
            // TODO: handle question_mark
            let b_question_mark = *b.contains_question_mark.as_ref().unwrap();
            b.stmts
                .push(add_ok_if_result(mutated_info.stmt.clone(), b_question_mark));
            
            let mut_tuple = |prefix: String| -> RcDoc<'a> {
                // if there is only one element, just print the identifier instead of making a tuple
                if mutated_info.vars.0.len() == 1 {
                    match mutated_info.vars.0.iter().next() {
                        None => RcDoc::nil(),
                        Some(i) => 
                        translate_ident(Ident::Local(i.clone()))
                    }
                } 
                // print as tuple otherwise
                else {
                    RcDoc::as_string(prefix)
                    .append(make_tuple(mutated_info
                        .vars
                        .0
                        .iter()
                        .sorted()
                        .map(|i| translate_ident(Ident::Local(i.clone())))))
                }
            };
            let loop_expr = RcDoc::as_string("foldi")
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e1.clone(), top_ctx)))
                .append(RcDoc::space())
                .append(make_paren(translate_expression(e2.clone(), top_ctx)))
                .append(RcDoc::space())
                .append(RcDoc::as_string("(fun"))
                .append(RcDoc::space())
                .append(translate_ident(x.clone()))
                .append(RcDoc::space())
                .append(mut_tuple("'".to_string()).clone())
                .append(RcDoc::space())
                .append(RcDoc::as_string("=>"))
                .append(RcDoc::line())
                .append(translate_block(b, true, top_ctx))
                .append(RcDoc::as_string(")"))
                .group()
                .nest(2)
                .append(RcDoc::line())
                .append(mut_tuple("".to_string()).clone());
                
                make_let_binding(mut_tuple("'".to_string()), None, loop_expr, false)
                .append(RcDoc::hardline())
                .append(translate_statements(statements, top_ctx))
                
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
                Statement::ReturnExp(Expression::Lit(Literal::Unit)),
                DUMMY_SP.into(),
            ));
        }
        (Some(_), _) => (),
    }
    translate_statements(statements.iter(), top_ctx).group()
}

fn translate_item<'a>(i: &'a Item, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    match i {
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
            .append(if let BaseTyp::Unit = sig.ret.0 {
                RcDoc::hardline().append(RcDoc::as_string("()"))
            } else {
                RcDoc::nil()
            })
            .group(),
            true,
        ),
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
                        .append(translate_enum_case_name(name_ty, case_name.0.clone()))
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
            RcDoc::as_string(".").append(RcDoc::line()),
        )),
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
            Some(index_typ) => {
                RcDoc::hardline()
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
                .append(make_uint_size_coercion(
                    translate_ident(Ident::TopLevel(index_typ.0.clone()))))
            }
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
            let canvas_size_bytes = RcDoc::as_string(format!("{}", (canvas_size + 7) / 8));
            (match info {
                Some((canvas_name, _modulo)) =>
                    RcDoc::as_string("Definition")
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
                ),
            )
        }
        Item::ImportedCrate((TopLevelIdent(kr), _)) => RcDoc::as_string(format!(
            "Require Import {}.",
            str::replace(&kr.to_title_case(), " ", ".")
        )),
        // Aliases are translated to Coq Notations
        Item::AliasDecl((TopLevelIdent(name), _), (ty, _)) => RcDoc::as_string("Notation")
            .append(RcDoc::space())
            .append(RcDoc::as_string("\"'"))
            .append(translate_ident_str(name.clone()))
            .append(RcDoc::as_string("'\""))
            .append(RcDoc::space())
            .append(RcDoc::as_string(":= ("))
            .append(translate_base_typ(ty.clone()))
            .append(RcDoc::as_string(") : hacspec_scope.")),
    }
}
    
fn translate_program<'a>(p: &'a Program, top_ctx: &'a TopLevelContext) -> RcDoc<'a, ()> {
    RcDoc::concat(p.items.iter().map(|(i, _)| {
        translate_item(i, top_ctx)
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
        "Require Import Lib MachineIntegers.\n\
        From Coq Require Import ZArith.\n\
        Import List.ListNotations.\n\
        Open Scope Z_scope.\n\
        Open Scope bool_scope.\n\
        Open Scope hacspec_scope.\n"
    )
    .unwrap();
    translate_program(p, top_ctx).render(width, &mut w).unwrap();
    write!(file, "{}", String::from_utf8(w).unwrap()).unwrap()
}
