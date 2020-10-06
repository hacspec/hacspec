use core::cmp::PartialEq;
use core::hash::Hash;
use im::HashSet;
use itertools::Itertools;
use rustc_ast::ast::BinOpKind;
use rustc_span::Span;
use std::fmt;

pub type Spanned<T> = (T, Span);

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub struct HacspecId(pub usize);

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Ident {
    Original(String),
    Hacspec(HacspecId, String),
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Ident::Original(n) => n.clone(),
                Ident::Hacspec(x, n) => format!("{}_{}", n, x.0),
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

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum ArraySize {
    Integer(usize),
    Ident(String),
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Secrecy {
    Secret,
    Public,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum BaseTyp {
    Unit,
    Bool,
    UInt128,
    Int128,
    UInt64,
    Int64,
    UInt32,
    Int32,
    UInt16,
    Int16,
    UInt8,
    Int8,
    Usize,
    Isize,
    Str,
    Seq(Box<Spanned<BaseTyp>>),
    Array(Spanned<ArraySize>, Box<Spanned<BaseTyp>>),
    Named(Spanned<Ident>, Option<Vec<Spanned<BaseTyp>>>),
    Variable(HacspecId),
    Tuple(Vec<Spanned<BaseTyp>>),
    NaturalInteger(Secrecy, Spanned<String>, Spanned<usize>), // secrecy, modulo value, encoding bits
}

impl fmt::Display for BaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseTyp::Unit => write!(f, "unit"),
            BaseTyp::Bool => write!(f, "bool"),
            BaseTyp::UInt128 => write!(f, "u128"),
            BaseTyp::Int128 => write!(f, "i128"),
            BaseTyp::UInt64 => write!(f, "u64"),
            BaseTyp::Int64 => write!(f, "i64"),
            BaseTyp::UInt32 => write!(f, "u32"),
            BaseTyp::Int32 => write!(f, "i32"),
            BaseTyp::UInt16 => write!(f, "u16"),
            BaseTyp::Int16 => write!(f, "i16"),
            BaseTyp::UInt8 => write!(f, "u8"),
            BaseTyp::Int8 => write!(f, "i8"),
            BaseTyp::Usize => write!(f, "usize"),
            BaseTyp::Isize => write!(f, "isize"),
            BaseTyp::Str => write!(f, "string"),
            BaseTyp::Array(size, mu) => {
                let mu = &mu.0;
                write!(f, "Array<{:?}, {}>", size.0, mu)
            }
            BaseTyp::Seq(mu) => {
                let mu = &mu.0;
                write!(f, "Seq<{}>", mu)
            }
            BaseTyp::Named(ident, args) => write!(
                f,
                "{}{}",
                ident.0,
                match args {
                    None => String::new(),
                    Some(args) => format!("<{}>", args.iter().map(|(x, _)| x).format(", ")),
                }
            ),
            BaseTyp::Tuple(args) => write!(
                f,
                "({})",
                args.iter().map(|(arg, _)| format!("{}", arg)).format(", ")
            ),
            BaseTyp::Variable(id) => write!(f, "T[{}]", id.0),
            BaseTyp::NaturalInteger(sec, modulo, bits) => {
                write!(f, "nat[{:?}][modulo {}][bits {}]", sec, modulo.0, bits.0)
            }
        }
    }
}

impl fmt::Debug for BaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

#[derive(Clone)]
pub enum Literal {
    Unit,
    Bool(bool),
    Int128(i128),
    UInt128(u128),
    Int64(i64),
    UInt64(u64),
    Int32(i32),
    UInt32(u32),
    Int16(i16),
    UInt16(u16),
    Int8(i8),
    UInt8(u8),
    Usize(usize),
    Isize(isize),
    Str(String),
}

#[derive(Clone)]
pub enum UnOpKind {
    Not,
    Neg,
}

#[derive(Clone)]
pub enum Expression {
    Unary(UnOpKind, Box<Spanned<Expression>>, Option<Typ>),
    Binary(
        Spanned<BinOpKind>,
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
        Option<Typ>,
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
    IntegerCasting(Box<Spanned<Expression>>, Spanned<BaseTyp>),
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
    ArrayDecl(
        Spanned<Ident>,         // Name of the array type
        Spanned<Expression>,    // Length
        Spanned<BaseTyp>,       // Cell type
        Option<Spanned<Ident>>, // Optional type alias for indexes
    ),
    ConstDecl(Spanned<Ident>, Spanned<BaseTyp>, Spanned<Expression>),
    NaturalIntegerDecl(
        Spanned<Ident>, // Element type name
        Spanned<Ident>, // Canvas array type name
        Secrecy,
        Spanned<Expression>,
        Spanned<String>,
    ),
}

pub struct Program {
    pub items: Vec<Spanned<Item>>,
    pub imported_crates: Vec<Spanned<String>>,
}
