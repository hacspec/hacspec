use core::cmp::PartialEq;
use core::hash::Hash;
use im::HashSet;
use itertools::Itertools;
use rustc_ast::ast::BinOpKind;
use rustc_span::Span;
use std::fmt;

pub type Spanned<T> = (T, Span);

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub struct RustspecId(pub usize);

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Ident {
    Original(String),
    Rustspec(RustspecId, String),
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Ident::Original(n) => n.clone(),
                Ident::Rustspec(x, n) => format!("{}_{}", n, x.0),
            }
        )
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub type VarSet = HashSet<Ident>;

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Borrowing {
    Borrowed,
    Consumed,
}

impl fmt::Display for Borrowing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Borrowing::Consumed => "",
                Borrowing::Borrowed => "&",
            },
        )
    }
}

impl fmt::Debug for Borrowing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum BaseTyp {
    Unit,
    Bool,
    UInt128(Secrecy),
    Int128(Secrecy),
    UInt64(Secrecy),
    Int64(Secrecy),
    UInt32(Secrecy),
    Int32(Secrecy),
    UInt16(Secrecy),
    Int16(Secrecy),
    UInt8(Secrecy),
    Int8(Secrecy),
    Usize,
    Isize,
    Seq(Box<Spanned<BaseTyp>>),
    Array(Spanned<usize>, Box<Spanned<BaseTyp>>),
    Named(Spanned<Ident>, Option<Box<Spanned<BaseTyp>>>),
    Variable(RustspecId),
    Tuple(Vec<Spanned<BaseTyp>>),
}

impl fmt::Display for BaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseTyp::Unit => write!(f, "unit"),
            BaseTyp::Bool => write!(f, "bool"),
            BaseTyp::UInt128(label) => write!(f, "u128[{}]", label),
            BaseTyp::Int128(label) => write!(f, "i128[{}]", label),
            BaseTyp::UInt64(label) => write!(f, "u64[{}]", label),
            BaseTyp::Int64(label) => write!(f, "i64[{}]", label),
            BaseTyp::UInt32(label) => write!(f, "u32[{}]", label),
            BaseTyp::Int32(label) => write!(f, "i32[{}]", label),
            BaseTyp::UInt16(label) => write!(f, "u16[{}]", label),
            BaseTyp::Int16(label) => write!(f, "i16[{}]", label),
            BaseTyp::UInt8(label) => write!(f, "u8[{}]", label),
            BaseTyp::Int8(label) => write!(f, "i8[{}]", label),
            BaseTyp::Usize => write!(f, "usize"),
            BaseTyp::Isize => write!(f, "isize"),
            BaseTyp::Array(size, mu) => {
                let mu = &mu.0;
                write!(f, "Array<{}, {}>", size.0, mu)
            }
            BaseTyp::Seq(mu) => {
                let mu = &mu.0;
                write!(f, "Seq<{}>", mu)
            }
            BaseTyp::Named(ident, arg) => write!(
                f,
                "{}{}",
                ident.0,
                match arg {
                    None => String::new(),
                    Some(arg) => format!("<{}>", arg.0),
                }
            ),
            BaseTyp::Tuple(args) => write!(
                f,
                "({})",
                args.iter().map(|(arg, _)| format!("{}", arg)).format(", ")
            ),
            BaseTyp::Variable(id) => write!(f, "T[{}]", id.0),
        }
    }
}

impl fmt::Debug for BaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Secrecy {
    Secret,
    Public,
}

impl fmt::Display for Secrecy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Secrecy::Public => "public",
                Secrecy::Secret => "secret",
            }
        )
    }
}

impl fmt::Debug for Secrecy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone)]
pub enum Literal {
    Unit,
    Bool(bool),
    Int128(i128, Secrecy),
    UInt128(u128, Secrecy),
    Int64(i64, Secrecy),
    UInt64(u64, Secrecy),
    Int32(i32, Secrecy),
    UInt32(u32, Secrecy),
    Int16(i16, Secrecy),
    UInt16(u16, Secrecy),
    Int8(i8, Secrecy),
    UInt8(u8, Secrecy),
    Usize(usize),
    Isize(isize),
}

#[derive(Clone)]
pub enum UnOpKind {
    Not,
    Neg,
}

#[derive(Clone)]
pub enum Expression {
    Unary(UnOpKind, Box<Spanned<Expression>>),
    Binary(
        Spanned<BinOpKind>,
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
    ),
    Named(Ident),
    // FuncCall(prefix, name, args)
    FuncCall(
        Option<Spanned<BaseTyp>>,
        Spanned<Ident>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
    ),
    MethodCall(
        Box<(Spanned<Expression>, Spanned<Borrowing>)>,
        Option<Typ>, // Type of self, to be filled by the typechecker
        Spanned<Ident>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
    ),
    Lit(Literal),
    ArrayIndex(Spanned<Ident>, Box<Spanned<Expression>>),
    NewArray(Spanned<Ident>, Option<BaseTyp>, Vec<Spanned<Expression>>),
    Tuple(Vec<Spanned<Expression>>),
}

#[derive(Clone)]
pub enum Pattern {
    IdentPat(Ident),
    WildCard,
    Tuple(Vec<Spanned<Pattern>>),
}

#[derive(Clone)]
pub struct MutatedInfo {
    pub vars: VarSet,
    pub stmt: Statement,
}

pub type Fillable<T> = Option<T>;

#[derive(Clone)]
pub enum Statement {
    LetBinding(Spanned<Pattern>, Option<Spanned<Typ>>, Spanned<Expression>),
    Reassignment(Spanned<Ident>, Spanned<Expression>),
    Conditional(
        Spanned<Expression>,
        Spanned<Block>,
        Option<Spanned<Block>>,
        Fillable<Box<MutatedInfo>>,
    ),
    ForLoop(
        Spanned<Ident>,
        Spanned<Expression>,
        Spanned<Expression>,
        Spanned<Block>,
    ),
    ArrayUpdate(Spanned<Ident>, Spanned<Expression>, Spanned<Expression>),
    ReturnExp(Expression),
}

#[derive(Clone)]
pub struct Block {
    pub stmts: Vec<Spanned<Statement>>,
    pub mutated: Fillable<Box<MutatedInfo>>,
    pub return_typ: Fillable<Typ>,
}

#[derive(Clone, Debug)]
pub struct FuncSig {
    pub args: Vec<(Spanned<Ident>, Spanned<Typ>)>,
    pub ret: Spanned<BaseTyp>,
}

#[derive(Clone, Debug)]
pub struct ExternalFuncSig {
    pub args: Vec<Typ>,
    pub ret: BaseTyp,
}

#[derive(Clone)]
pub enum Item {
    FnDecl(Spanned<Ident>, FuncSig, Spanned<Block>),
    ArrayDecl(Spanned<Ident>, Spanned<usize>, Spanned<BaseTyp>),
}

pub struct Program {
    pub items: Vec<Spanned<Item>>,
    pub imported_crates: Vec<Spanned<String>>,
}
