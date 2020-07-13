use rustc_span::{symbol::Ident, Span};
use rustc_ast::ast::Mutability;

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
    Int,
    Seq(Box<Spanned<BaseTyp>>),
    Named(Path),
    Tuple(Vec<Spanned<BaseTyp>>),
}

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

pub enum Expression {}

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
