use rustc_ast::ast::{BinOpKind, Mutability, UnOp};
use rustc_span::{symbol::Ident, Span};

pub type Spanned<T> = (T, Span);

pub enum Borrowing {
    Borrowed,
    Consumed,
}

pub struct Path {
    pub location: Vec<Ident>,
    pub arg: Option<Box<BaseTyp>>,
}

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
    Seq(Box<Spanned<BaseTyp>>),
    Named(Path),
    Tuple(Vec<Spanned<BaseTyp>>),
}

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

pub enum Literal {
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
}

pub enum Expression {
    Unary(UnOp, Box<Spanned<Expression>>),
    Binary(
        Spanned<BinOpKind>,
        Box<Spanned<Expression>>,
        Box<Spanned<Expression>>,
    ),
    Named(Path),
    FuncCall(Spanned<Path>, Vec<Spanned<Expression>>),
    Lit(Literal),
    ArrayIndex(Box<Spanned<Expression>>, Box<Spanned<Expression>>),
    Tuple(Vec<Spanned<Expression>>),
}

pub enum Pattern {
    IdentPat(Ident, Mutability),
    WildCard,
    Tuple(Vec<Spanned<Pattern>>),
}

pub enum Statement {
    LetBinding(Spanned<Pattern>, Option<Spanned<Typ>>, Spanned<Expression>),
    Reassignment(Ident, Spanned<Expression>),
    Conditional(Spanned<Expression>, Spanned<Block>, Option<Spanned<Block>>),
    ForLoop(
        Ident,
        Spanned<Expression>,
        Spanned<Expression>,
        Spanned<Block>,
    ),
    ArrayUpdate(Ident, Spanned<Expression>, Spanned<Expression>),
    ReturnExp(Expression),
}

pub type Block = Vec<Spanned<Statement>>;

pub struct FuncSig {
    pub args: Vec<(Spanned<Ident>, Spanned<Typ>)>,
    pub ret: Spanned<BaseTyp>,
}

pub enum Item {
    FnDecl((Ident, FuncSig, Spanned<Block>)),
}

pub type Program = Vec<Spanned<Item>>;
