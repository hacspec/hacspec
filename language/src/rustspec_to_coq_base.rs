use crate::name_resolution::{DictEntry, TopLevelContext};
use crate::rustspec::*;
use core::iter::IntoIterator;
use heck::SnakeCase;
use lazy_static::lazy_static;
use pretty::RcDoc;
use regex::Regex;
use rustc_span::DUMMY_SP;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

pub(crate) const SEQ_MODULE: &'static str = "seq";
pub(crate) const ARRAY_MODULE: &'static str = "array";
pub(crate) const NAT_MODULE: &'static str = "nat_mod";
static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub(crate) fn fresh_codegen_id() -> usize {
    ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

lazy_static! {
    static ref ID_MAP: Mutex<HashMap<usize, usize>> = Mutex::new(HashMap::new());
}

pub(crate) fn translate_ident<'a>(x: Ident) -> RcDoc<'a, ()> {
    match x {
        Ident::Unresolved(s) => translate_ident_str(s.clone()),
        Ident::TopLevel(s) => translate_toplevel_ident(s),
        Ident::Local(LocalIdent { id, name: s, .. }) => {
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

pub(crate) fn translate_toplevel_ident<'a>(x: TopLevelIdent) -> RcDoc<'a, ()> {
    match x.kind {
        TopLevelIdentKind::Type => {
            match format!("{}", translate_ident_str(x.string).pretty(0)).as_str() {
                s @ "uint128"
                | s @ "uint64"
                | s @ "uint32"
                | s @ "uint16"
                | s @ "uint8"
                | s @ "int128"
                | s @ "int64"
                | s @ "int32"
                | s @ "int16"
                | s @ "int8"
                | s @ "byte_seq"
                | s @ "public_byte_seq"
                | s @ "option"
                | s @ "result" => RcDoc::as_string(s),
                s => RcDoc::as_string(format!("{}_t", s)),
            }
        }
        TopLevelIdentKind::Constant => translate_ident_str(format!("{}_v", x.string)),
        _ => translate_ident_str(x.string),
    }
}

pub(crate) fn translate_ident_str<'a>(ident_str: String) -> RcDoc<'a, ()> {
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

pub(crate) fn make_uint_size_coercion<'a>(pat: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
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

pub(crate) fn make_tuple<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
    let mut iter = args.into_iter();
    match &iter.size_hint().1 {
        Some(0) => RcDoc::as_string("tt"),
        Some(1) => iter.next().unwrap(),
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

pub(crate) fn make_list<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
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

pub(crate) fn make_typ_tuple<'a, I: IntoIterator<Item = RcDoc<'a, ()>>>(args: I) -> RcDoc<'a, ()> {
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

pub(crate) fn make_paren<'a>(e: RcDoc<'a, ()>) -> RcDoc<'a, ()> {
    RcDoc::as_string("(")
        .append(RcDoc::softline_().append(e).group().nest(2))
        .append(RcDoc::as_string(")"))
        .group()
}

pub(crate) fn translate_binop<'a, 'b>(
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
                        BinOpKind::Add => return RcDoc::as_string("+%"),
                        BinOpKind::Sub => return RcDoc::as_string("-%"),
                        BinOpKind::Mul => return RcDoc::as_string("*%"),
                        BinOpKind::Div => return RcDoc::as_string("/%"),
                        BinOpKind::Rem => return RcDoc::as_string("rem"),
                        // Rem,
                        // And,
                        // Or,
                        BinOpKind::BitXor => return RcDoc::as_string("xor"),
                        BinOpKind::BitOr => return RcDoc::as_string("or"),
                        BinOpKind::BitAnd => return RcDoc::as_string("and"),
                        // Shl,
                        // Shr,
                        BinOpKind::Eq => return RcDoc::as_string("=.?"),
                        BinOpKind::Lt => return RcDoc::as_string("<.?"),
                        BinOpKind::Le => return RcDoc::as_string("<=.?"),
                        BinOpKind::Ne => return RcDoc::as_string("!=.?"),
                        BinOpKind::Ge => return RcDoc::as_string(">=.?"),
                        BinOpKind::Gt => return RcDoc::as_string(">.?"),
                        _ => unimplemented!("{:?}", op),
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
            RcDoc::as_string(".-")
        }
        (BinOpKind::Add, BaseTyp::Usize) | (BinOpKind::Add, BaseTyp::Isize) => {
            RcDoc::as_string(".+")
        }
        (BinOpKind::Mul, BaseTyp::Usize) | (BinOpKind::Mul, BaseTyp::Isize) => {
            RcDoc::as_string(".*")
        }
        (BinOpKind::Div, BaseTyp::Usize) | (BinOpKind::Div, BaseTyp::Isize) => {
            RcDoc::as_string("./")
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

pub(crate) fn translate_unop<'a>(op: UnOpKind, _op_typ: Typ) -> RcDoc<'a, ()> {
    match (op, &(_op_typ.1).0) {
        (UnOpKind::Not, BaseTyp::Bool) => RcDoc::as_string("negb"),
        (UnOpKind::Not, _) => RcDoc::as_string("not"),
        (UnOpKind::Neg, _) => RcDoc::as_string("-"),
    }
}

// taken from rustspec_to_fstar
pub(crate) fn array_or_seq<'a>(t: Typ, top_ctxt: &'a TopLevelContext) -> RcDoc<'a, ()> {
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
pub(crate) fn add_ok_if_result(
    stmt: Statement,
    early_return_type: Fillable<CarrierTyp>,
    question_mark: Option<ScopeMutableVars>,
) -> Spanned<Statement> {
    (
        match early_return_type {
            Some(ert) => {
                match question_mark {
                    Some(_) =>
                    // If b has an early return, then we must prefix the returned
                    // mutated variables by Ok or Some
                    {
                        match stmt {
                            Statement::ReturnExp(e, Some((x, t_base))) => {
                                let (early_typ, fun_name) = match ert.clone() {
                                    CarrierTyp::Option(a) => (
                                        BaseTyp::Named(
                                            (
                                                TopLevelIdent {
                                                    string: "Option".to_string(),
                                                    kind: TopLevelIdentKind::Type,
                                                },
                                                DUMMY_SP.into(),
                                            ),
                                            Some(vec![t_base.clone()]),
                                        ),
                                        "Some",
                                    ),
                                    CarrierTyp::Result(a, b) => (
                                        BaseTyp::Named(
                                            (
                                                TopLevelIdent {
                                                    string: "Result".to_string(),
                                                    kind: TopLevelIdentKind::Type,
                                                },
                                                DUMMY_SP.into(),
                                            ),
                                            Some(vec![t_base.clone(), b]),
                                        ),
                                        "Ok",
                                    ),
                                };

                                Statement::ReturnExp(
                                    Expression::EnumInject(
                                        early_typ.clone(),
                                        (
                                            TopLevelIdent {
                                                string: fun_name.to_string(),
                                                kind: TopLevelIdentKind::EnumConstructor,
                                            },
                                            DUMMY_SP.into(),
                                        ),
                                        Some((Box::new(e.clone()), DUMMY_SP.into())),
                                    ),
                                    Some((x, (early_typ.clone(), t_base.1))),
                                )
                            },
                            _ => panic!("should not happen"),
                        }
                    }
                    None => stmt.clone(),
                }
            }
            _ => stmt.clone(),
        },
        DUMMY_SP.into(),
    )
}

#[derive(Debug)]
pub(crate) enum FuncPrefix {
    Regular,
    Array(ArraySize, BaseTyp),
    Seq(BaseTyp),
    NatMod(String, usize), // Modulo value, number of bits for the encoding,
}

pub(crate) fn translate_prefix_for_func_name<'a>(
    prefix: BaseTyp,
    top_ctx: &'a TopLevelContext,
) -> (RcDoc<'a, ()>, FuncPrefix) {
    match prefix {
        BaseTyp::Bool => panic!(), // should not happen
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
        BaseTyp::Tuple(args) => panic!("{:?}", args),    // should not happen
        BaseTyp::NaturalInteger(_, modulo, bits) => (
            RcDoc::as_string(NAT_MODULE),
            FuncPrefix::NatMod(modulo.0.clone(), bits.0.clone()),
        ),
    }
}
