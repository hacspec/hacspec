use core::cmp::PartialEq;
use core::hash::Hash;
use im::HashSet;
use itertools::Itertools;
use rustc_span::{MultiSpan, Span};
use serde::{ser::SerializeSeq, Serialize, Serializer};
use std::fmt;

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug, Copy)]
pub struct RustspecSpan(pub Span);

impl Serialize for RustspecSpan {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(format!("{:?}", self.0).as_str())
    }
}

pub type Spanned<T> = (T, RustspecSpan);

impl From<RustspecSpan> for MultiSpan {
    fn from(x: RustspecSpan) -> MultiSpan {
        x.0.into()
    }
}

impl From<Span> for RustspecSpan {
    fn from(x: Span) -> RustspecSpan {
        RustspecSpan(x)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct LocalIdent {
    pub id: usize,
    pub name: String,
}

impl fmt::Display for LocalIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}_{}", self.name, self.id)
    }
}

impl fmt::Debug for LocalIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Debug)]
pub enum TopLevelIdentKind {
    Type,
    Function,
    Constant,
    Crate,
    EnumConstructor,
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct TopLevelIdent {
    pub string: String,
    pub kind: TopLevelIdentKind,
}

impl fmt::Display for TopLevelIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.string)
    }
}

impl fmt::Debug for TopLevelIdent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum Ident {
    Unresolved(String),
    Local(LocalIdent),
    TopLevel(TopLevelIdent),
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Ident::Unresolved(n) => n.clone(),
                Ident::Local(n) => format!("{}", n),
                Ident::TopLevel(n) => format!("{}", n),
            }
        )
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct VarSet(pub HashSet<LocalIdent>);

impl Serialize for VarSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for e in &self.0 {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Serialize)]
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

#[derive(Clone, Hash, PartialEq, Eq, Debug, Serialize)]
pub enum ArraySize {
    Integer(usize),
    Ident(TopLevelIdent),
}

#[derive(Clone, Hash, PartialEq, Eq, Debug, Serialize)]
pub enum Secrecy {
    Secret,
    Public,
}

#[derive(Clone, Hash, PartialEq, Eq, Serialize)]
pub struct TypVar(pub usize);

impl fmt::Display for TypVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "T[{}]", self.0)
    }
}

impl fmt::Debug for TypVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Serialize)]
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
    Named(Spanned<TopLevelIdent>, Option<Vec<Spanned<BaseTyp>>>),
    Variable(TypVar),
    Tuple(Vec<Spanned<BaseTyp>>),
    Enum(
        Vec<(Spanned<TopLevelIdent>, Option<Spanned<BaseTyp>>)>,
        Vec<TypVar>,
    ), // Cases, type variables
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
            BaseTyp::Enum(args, _) => write!(
                f,
                "[{}]",
                args.iter()
                    .map(|((case, _), payload)| match payload {
                        Some((payload, _)) => format!("{}: {}", case, payload),
                        None => format!("{}", case),
                    })
                    .format(" | ")
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

#[derive(Clone, Serialize, Debug)]
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

#[derive(Clone, Serialize, Debug)]
pub enum UnOpKind {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, Serialize)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

#[derive(Clone, Serialize, Debug)]
pub enum Expression {
    Unary(UnOpKind, Box<Spanned<Expression>>, Option<Typ>),
    Binary(
        Spanned<BinOpKind>,
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
        Option<Typ>,
    ),
    InlineConditional(
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
    ),
    Named(Ident),
    // FuncCall(prefix, name, args)
    FuncCall(
        Option<Spanned<BaseTyp>>,
        Spanned<TopLevelIdent>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
    ),
    MethodCall(
        Box<(Spanned<Expression>, Spanned<Borrowing>)>,
        Option<Typ>, // Type of self, to be filled by the typechecker
        Spanned<TopLevelIdent>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
    ),
    EnumInject(
        BaseTyp,                          // Type of enum
        Spanned<TopLevelIdent>,           // Name of case
        Option<Spanned<Box<Expression>>>, // Payload of case
    ),
    MatchWith(
        Box<Spanned<Expression>>, // Expression to match
        Vec<(
            BaseTyp,                  // Type of enum
            Spanned<TopLevelIdent>,   // Name of case
            Option<Spanned<Pattern>>, // Payload of case
            Spanned<Expression>,      // Match arm expression
        )>,
    ),
    Lit(Literal),
    ArrayIndex(
        Spanned<Ident>,           // Array variable
        Box<Spanned<Expression>>, // Index
        Fillable<Typ>,            // Type of the array
    ),
    NewArray(
        Option<Spanned<TopLevelIdent>>, // Name of array type, None if Seq
        Option<BaseTyp>,                // Type of cells
        Vec<Spanned<Expression>>,       // Contents
    ),
    Tuple(Vec<Spanned<Expression>>),
    IntegerCasting(
        Box<Spanned<Expression>>, //expression to cast
        Spanned<BaseTyp>,         // destination type
        Option<BaseTyp>,          // origin type
    ),
}

#[derive(Clone, Serialize, Debug)]
pub enum Pattern {
    IdentPat(Ident),
    WildCard,
    Tuple(Vec<Spanned<Pattern>>),
    SingleCaseEnum(Spanned<TopLevelIdent>, Box<Spanned<Pattern>>),
}

#[derive(Clone, Serialize, Debug)]
pub enum EarlyReturnType {
    Option,
    Result,
}

#[derive(Clone, Serialize, Debug)]
pub struct MutatedInfo {
    pub early_return_type: Fillable<EarlyReturnType>,
    pub vars: VarSet,
    pub stmt: Statement,
}

pub type Fillable<T> = Option<T>;

#[derive(Clone, Serialize, Debug)]
pub enum Statement {
    LetBinding(
        Spanned<Pattern>,     // Let-binded pattern
        Option<Spanned<Typ>>, // Typ of the binded expr
        Spanned<Expression>,  // Binded expr
        bool,                 // Presence of a question mark at the end
    ),
    Reassignment(
        Spanned<Ident>,      // Variable reassigned
        Spanned<Expression>, // New value
        bool,                // Presence of a question mark at the end
    ),
    Conditional(
        Spanned<Expression>,        // Condition
        Spanned<Block>,             // Then block
        Option<Spanned<Block>>,     // Else block
        Fillable<Box<MutatedInfo>>, // Variables mutated in either branch
    ),
    ForLoop(
        Option<Spanned<Ident>>, // Loop variable
        Spanned<Expression>,    // Lower bound
        Spanned<Expression>,    // Upper bound
        Spanned<Block>,         // Loop body
    ),
    ArrayUpdate(
        Spanned<Ident>,      // Array variable
        Spanned<Expression>, // Index value
        Spanned<Expression>, // Cell value
        bool,                // Presence of a question mark at the end of the cell value expression
        Fillable<Typ>,       // Type of the array
    ),
    ReturnExp(Expression),
}

#[derive(Clone, Serialize, Debug)]
pub struct Block {
    pub stmts: Vec<Spanned<Statement>>,
    pub mutated: Fillable<Box<MutatedInfo>>,
    pub return_typ: Fillable<Typ>,
    pub contains_question_mark: Fillable<bool>,
}

#[derive(Clone, Debug, Serialize)]
pub struct FuncSig {
    pub args: Vec<(Spanned<Ident>, Spanned<Typ>)>,
    pub ret: Spanned<BaseTyp>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ExternalFuncSig {
    pub args: Vec<Typ>,
    pub ret: BaseTyp,
}

#[derive(Clone, Serialize)]
pub enum Item {
    FnDecl(Spanned<TopLevelIdent>, FuncSig, Spanned<Block>),
    EnumDecl(
        Spanned<TopLevelIdent>,
        Vec<(Spanned<TopLevelIdent>, Option<Spanned<BaseTyp>>)>,
    ),
    ArrayDecl(
        Spanned<TopLevelIdent>,         // Name of the array type
        Spanned<Expression>,            // Length
        Spanned<BaseTyp>,               // Cell type
        Option<Spanned<TopLevelIdent>>, // Optional type alias for indexes
    ),
    AliasDecl(Spanned<TopLevelIdent>, Spanned<BaseTyp>),
    ImportedCrate(Spanned<TopLevelIdent>),
    ConstDecl(
        Spanned<TopLevelIdent>,
        Spanned<BaseTyp>,
        Spanned<Expression>,
    ),
    NaturalIntegerDecl(
        Spanned<TopLevelIdent>,                            // Element type name
        Secrecy,                                           // Public or secret
        Spanned<Expression>,                               // Canvas size
        Option<(Spanned<TopLevelIdent>, Spanned<String>)>, // Canvas array type name and modulo value
    ),
}

pub type ItemTag = String;

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct ItemTagSet(pub HashSet<ItemTag>);

impl Serialize for ItemTagSet {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for e in &self.0 {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

#[derive(Clone, Serialize)]
pub struct DecoratedItem {
    pub item: Item,
    pub tags: ItemTagSet,
}

#[derive(Clone, Serialize)]
pub struct Program {
    pub items: Vec<Spanned<DecoratedItem>>,
}

// Helpers

#[allow(non_snake_case)]
pub fn U8_TYP() -> TopLevelIdent {
    TopLevelIdent {
        string: "U8".into(),
        kind: TopLevelIdentKind::Type,
    }
}
