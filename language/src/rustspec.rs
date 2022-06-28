use core::cmp::PartialEq;
use core::hash::Hash;
use im::HashSet;
use itertools::Itertools;
use rustc_errors::MultiSpan;
use rustc_span::Span;
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
    pub mutable: bool,
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

#[derive(Clone, Hash, PartialEq, Eq, Serialize, Debug)]
pub enum BaseTyp {
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

pub const UnitTyp: BaseTyp = BaseTyp::Tuple(vec!());

impl fmt::Display for BaseTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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

// impl fmt::Debug for BaseTyp {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self)
//     }
// }

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

/// Enumeration of the types allowed as question marks's monad
/// representation. Named after the [Carrier][std::ops::Carrier]
/// trait.
#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub enum CarrierTyp {
    Result(Spanned<BaseTyp>, Spanned<BaseTyp>),
    Option(Spanned<BaseTyp>),
}

/// Extracts the payload type of a carrier type, i.e., `A` is the
/// payload type of `Either<A, B>`.
pub fn carrier_payload(carrier: CarrierTyp) -> Spanned<BaseTyp> {
    match carrier {
        CarrierTyp::Result(ok, ..) | CarrierTyp::Option(ok, ..) => ok,
    }
}
pub fn carrier_kind(carrier: CarrierTyp) -> EarlyReturnType {
    match carrier {
        CarrierTyp::Result(..) => EarlyReturnType::Result,
        CarrierTyp::Option(..) => EarlyReturnType::Option,
    }
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
    QuestionMark(
        Box<Spanned<Expression>>,
        Fillable<CarrierTyp>, // Filled by typechecking phase
    ),
    /// One or multiple monadic bindings. For instance, `MonadicLet(M, [(x₀, e₀), …, (xₙ, eₙ)], «f x₀ … xₙ», true)` represents:
    /// ```haskell
    /// do x₀ <- e₀
    ///    …
    ///    xₙ <- eₙ
    ///    return $ f x₀ … xₙ
    /// ```
    /// Note the boolean flag indicates whether we shall insert a `pure` monadic operation or not (that is, above, shall we have `return $ f x₀ … xₙ` or simply `f x₀ … xₙ`).
    /// This node appears only after the [question marks elimination][desugar::eliminate_question_marks_in_expressions] phase.
    MonadicLet(
        CarrierTyp,                             // Are we dealing with `Result` or `Option`?
        Vec<(Ident, Box<Spanned<Expression>>)>, // List of "monadic" bindings
        Box<Spanned<Expression>>,               // body
        bool, // should we insert a `pure` node? (`pure` being e.g. `Ok`)
    ),
    Named(Ident),
    // FuncCall(prefix, name, args, arg_types)
    FuncCall(
        Option<Spanned<BaseTyp>>,
        Spanned<TopLevelIdent>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
        Fillable<Vec<BaseTyp>>,
    ),
    MethodCall(
        Box<(Spanned<Expression>, Spanned<Borrowing>)>,
        Option<Typ>, // Type of self, to be filled by the typechecker
        Spanned<TopLevelIdent>,
        Vec<(Spanned<Expression>, Spanned<Borrowing>)>,
        Fillable<Vec<BaseTyp>>,
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
    IdentPat(Ident, bool),
    WildCard,
    Tuple(Vec<Spanned<Pattern>>),
    SingleCaseEnum(Spanned<TopLevelIdent>, Box<Spanned<Pattern>>),
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub enum EarlyReturnType {
    Option(Spanned<BaseTyp>),
    Result(Spanned<BaseTyp>, Spanned<BaseTyp>),
}

#[derive(Clone, Serialize, Debug)]
pub struct MutatedInfo {
    pub early_return_type: Fillable<EarlyReturnType>,
    pub vars: VarSet,
    pub stmt: Statement,
}

pub type Fillable<T> = Option<T>;

pub type QuestionMarkInfo = Option<(ScopeMutableVars, FunctionDependencies, Fillable<EarlyReturnType>)>;

#[derive(Clone, Serialize, Debug)]
pub enum Statement {
    LetBinding(
        Spanned<Pattern>,     // Let-binded pattern
        Option<Spanned<Typ>>, // Typ of the binded expr
        Spanned<Expression>,  // Binded expr
        QuestionMarkInfo,     // Presence of a question mark at the end
    ),
    Reassignment(
        Spanned<Ident>,         // Variable reassigned
        Fillable<Spanned<Typ>>, // Type of variable reassigned
        Spanned<Expression>,    // New value
        QuestionMarkInfo,       // Presence of a question mark at the end
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
        QuestionMarkInfo,    // Presence of a question mark at the end of the cell value expression
        Fillable<Typ>,       // Type of the array
    ),
    ReturnExp(Expression, Fillable<Typ>),
}

pub type MutableVar = (Ident, Fillable<Typ>);
#[derive(Clone, Debug)]
pub struct ScopeMutableVars {
    pub external_vars: HashSet<MutableVar>,
    pub local_vars: HashSet<MutableVar>,
}

impl Serialize for ScopeMutableVars {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // TODO: Serialize local vars
        let mut seq = serializer.serialize_seq(Some(self.external_vars.len()))?;
        for e in &self.external_vars {
            seq.serialize_element(e)?;
        }
        seq.end()
    }
}

impl ScopeMutableVars {
    pub fn new() -> Self {
        ScopeMutableVars {
            external_vars: HashSet::new(),
            local_vars: HashSet::new(),
        }
    }

    pub fn push(&mut self, value: MutableVar) {
        self.local_vars.insert(value);
    }

    pub fn push_external(&mut self, value: MutableVar) {
        self.external_vars.insert(value);
    }

    pub fn extend(&mut self, other: ScopeMutableVars) {
        for i in other.external_vars {
            self.external_vars.insert(i);
        }
        for i in other.local_vars {
            self.local_vars.insert(i);
        }
    }

    pub fn extend_external(&mut self, other: ScopeMutableVars) {
        for i in other.external_vars {
            self.external_vars.insert(i);
        }
        for i in other.local_vars {
            self.external_vars.insert(i);
        }
    }

    pub fn subtract(self, other: ScopeMutableVars) -> ScopeMutableVars {
        ScopeMutableVars {
            external_vars: self.external_vars.clone().difference(other.external_vars),
            local_vars: self.local_vars.clone().difference(other.local_vars),
        }
    }
}

pub type FunctionDependency = TopLevelIdent;

#[derive(Clone, Debug)]
pub struct FunctionDependencies (pub HashSet<FunctionDependency>);

impl Serialize for FunctionDependencies {
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

#[derive(Clone, Debug, Serialize)]
pub struct Block {
    pub stmts: Vec<Spanned<Statement>>,
    pub mutated: Fillable<Box<MutatedInfo>>,
    pub return_typ: Fillable<Typ>,
    pub contains_question_mark: Fillable<bool>,
    pub mutable_vars: ScopeMutableVars,
    pub function_dependencies: FunctionDependencies,
}

#[derive(Clone, Debug, Serialize)]
pub struct FuncSig {
    pub args: Vec<(Spanned<Ident>, Spanned<Typ>)>,
    pub ret: Spanned<BaseTyp>,
    pub mutable_vars: ScopeMutableVars,
    pub function_dependencies: FunctionDependencies,
}

#[derive(Clone, Debug, Serialize)]
pub struct ExternalFuncSig {
    pub args: Vec<Typ>,
    pub ret: BaseTyp,
}

#[derive(Clone, Serialize, Debug)]
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

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
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

#[derive(Clone, Serialize, Debug)]
pub struct DecoratedItem {
    pub item: Item,
    pub tags: ItemTagSet,
}

#[derive(Clone, Serialize, Debug)]
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
