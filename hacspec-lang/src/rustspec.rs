use rustc_span::{symbol::Ident, Span};
use rustc_ast::ast::{Mutability, BinOpKind};

pub type Spanned<T> = (T, Span);

pub enum Borrowing {
    Borrowed,
    Consumed,
}

pub struct Path {
    pub location: Vec<Ident>,
    pub arg: Option<Box<BaseTyp>>
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
    Seq(Box<Spanned<BaseTyp>>),
    Named(Path),
    Tuple(Vec<Spanned<BaseTyp>>),
}

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

pub enum Literal {
    Bool(bool),
    Int32(i32),
    UnspecifiedInt(u128),
}

pub enum Expression {
    Binary(Spanned<BinOpKind>, Box<Spanned<Expression>>, Box<Spanned<Expression>>),
    Named(Path),
    FuncCall(Spanned<Path>, Vec<Spanned<Expression>>),
    Lit(Literal)
}

pub enum Pattern {
    IdentPat(Ident),
    WildCard
}

pub enum Statement {
    LetBinding(Pattern, Mutability, Option<Spanned<Typ>>, Spanned<Expression>),
    Reassignment(Ident, Spanned<Expression>),
    Conditional(Expression, Spanned<Block>, Spanned<Block>),
    ForLoop(Pattern, Spanned<Expression>, Spanned<Expression>, Spanned<Block>),
    ArrayUpdate(Ident, Spanned<Expression>, Spanned<Expression>),
    ReturnExp(Expression),
    SubBlock(Block)
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
