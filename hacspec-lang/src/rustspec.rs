use rustc_span::{symbol::Ident, Span};

pub type Spanned<T> = (T, Span);

pub enum Borrowing {
    Borrowed,
    Consumed,
}

pub enum BaseTyp {
    Unit,
    Bool,
    Int,
    Seq(Box<Spanned<BaseTyp>>),
    Named(Ident),
    Tuple(Vec<Box<Spanned<BaseTyp>>>),
}

pub enum Statement {}

pub type Block = Vec<Spanned<Statement>>;

pub type Typ = (Spanned<Borrowing>, Spanned<BaseTyp>);

pub struct FuncSig {
    pub args: Vec<(Spanned<Ident>, Spanned<Typ>)>,
    pub ret: Spanned<BaseTyp>,
}


pub enum Item {
    FnDecl((Ident, FuncSig, Spanned<Block>))
}

pub type Program = Vec<Spanned<Item>>;
