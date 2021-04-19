use std::fmt;

use im::HashMap;
use rustc_session::Session;

use crate::hir_to_rustspec::ExternalData;
use crate::rustspec::*;
use crate::HacspecErrorEmitter;
use rustc_span::DUMMY_SP;
use std::sync::atomic::{AtomicUsize, Ordering};

pub static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_hacspec_id() -> usize {
    ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

pub(crate) fn to_fresh_ident(x: &String) -> Ident {
    Ident::Local(LocalIdent {
        id: fresh_hacspec_id(),
        name: x.clone(),
    })
}

#[derive(Debug, Clone)]
pub enum DictEntry {
    Alias,
    Array,
    NaturalInteger,
}

pub type ResolutionResult<T> = Result<T, ()>;

pub type NameContext = HashMap<String, Ident>;

#[derive(Clone)]
pub struct TopLevelContext {
    pub functions: HashMap<FnKey, FnValue>,
    pub consts: HashMap<TopLevelIdent, Spanned<BaseTyp>>,
    pub typ_dict: HashMap<TopLevelIdent, (Typ, DictEntry)>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum FnKey {
    Independent(TopLevelIdent),
    Impl(BaseTyp, TopLevelIdent),
}

impl fmt::Display for FnKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                FnKey::Independent(ident) => format!("{}", ident),
                FnKey::Impl(t, n) => format!("{}::{}", t, n),
            }
        )
    }
}

impl fmt::Debug for FnKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub(crate) fn add_name(name: &Ident, var: &Ident, name_context: NameContext) -> NameContext {
    match name {
        Ident::Unresolved(name) => name_context.update(name.clone(), var.clone()),
        _ => panic!("trying to lookup in the name context a Hacspec id"),
    }
}

pub(crate) fn find_ident<'b>(
    sess: &Session,
    x: &Spanned<Ident>,
    name_context: &NameContext,
    top_level_context: &TopLevelContext,
) -> ResolutionResult<Ident> {
    match &x.0 {
        Ident::Unresolved(name) => match name_context.get(name) {
            None => {
                let x_tl = TopLevelIdent(name.clone());
                match top_level_context.consts.get(&x_tl) {
                    Some(_) => Ok(Ident::TopLevel(x_tl)),
                    None => {
                        sess.span_rustspec_err(x.1.clone(), "identifier is not a constant");
                        Err(())
                    }
                }
            }
            Some(id) => Ok(id.clone()),
        },
        _ => {
            sess.span_rustspec_err(
                x.1.clone(),
                "trying to lookup in the name context an already translated id",
            );
            Err(())
        }
    }
}

#[derive(Clone, Debug)]
pub enum FnValue {
    Local(FuncSig),
    External(ExternalFuncSig),
    ExternalNotInHacspec(String),
}

fn resolve_expression(
    _sess: &Session,
    (e, e_span): Spanned<Expression>,
    _name_context: &NameContext,
    _top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Expression>> {
    match e {
        _ => Ok((e, e_span)),
    }
}

fn resolve_pattern(
    sess: &Session,
    (pat, pat_span): &Spanned<Pattern>,
    top_ctx: &TopLevelContext,
) -> ResolutionResult<(Pattern, NameContext)> {
    match pat {
        Pattern::Tuple(pat_args) => {
            let (tup_args, acc_name) =
                pat_args
                    .iter()
                    .fold(Ok((Vec::new(), HashMap::new())), |acc, pat_arg| {
                        let (mut acc_pat, acc_name) = acc?;
                        let (new_pat, sub_name_context) = resolve_pattern(sess, pat_arg, top_ctx)?;
                        acc_pat.push((new_pat, pat_arg.1.clone()));
                        Ok((acc_pat, acc_name.union(sub_name_context)))
                    })?;
            Ok((Pattern::Tuple(tup_args), acc_name))
        }
        Pattern::WildCard => Ok((Pattern::WildCard, HashMap::new())),
        Pattern::IdentPat(x) => {
            let (x_new, s) = match x {
                Ident::Unresolved(s) => (to_fresh_ident(s), s.clone()),
                _ => panic!("should not happen"),
            };
            Ok((
                Pattern::IdentPat(x_new.clone()),
                HashMap::unit(s.clone(), x_new.clone()),
            ))
        }
    }
}

fn resolve_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    name_context: NameContext,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<(Spanned<Statement>, NameContext)> {
    match s {
        Statement::Conditional(cond, then_b, else_b, info) => {
            let new_cond = resolve_expression(sess, cond, &name_context, top_level_ctx)?;
            let new_then_b = resolve_block(sess, then_b, &name_context, top_level_ctx)?;
            let new_else_b = match else_b {
                None => None,
                Some(else_b) => {
                    let new_else_b = resolve_block(sess, else_b, &name_context, top_level_ctx)?;
                    Some(new_else_b)
                }
            };
            Ok((
                (
                    Statement::Conditional(new_cond, new_then_b, new_else_b, info),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::ForLoop((var, var_span), lower, upper, body) => {
            let new_lower = resolve_expression(sess, lower, &name_context, top_level_ctx)?;
            let new_upper = resolve_expression(sess, upper, &name_context, top_level_ctx)?;
            let new_var = match &var {
                Ident::Unresolved(s) => to_fresh_ident(s),
                _ => panic!("should not happen"),
            };
            let name_context = add_name(&var, &new_var, name_context);
            let new_body = resolve_block(sess, body, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::ForLoop((new_var, var_span), new_lower, new_upper, new_body),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::ReturnExp(e) => {
            let new_e =
                resolve_expression(sess, (e, s_span.clone()), &name_context, top_level_ctx)?;
            Ok(((Statement::ReturnExp(new_e.0), s_span), name_context))
        }
        Statement::ArrayUpdate(var, index, e) => {
            let new_var = find_ident(sess, &var, &name_context, top_level_ctx)?;
            let new_index = resolve_expression(sess, index, &name_context, top_level_ctx)?;
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::ArrayUpdate((new_var, var.1.clone()), new_index, new_e),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::Reassignment(var, e) => {
            let new_var = find_ident(sess, &var, &name_context, top_level_ctx)?;
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::Reassignment((new_var, var.1.clone()), new_e),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::LetBinding(pat, typ, e) => {
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            let (new_pat, new_name_context) = resolve_pattern(sess, &pat, top_level_ctx)?;
            let name_context = name_context.union(new_name_context);
            Ok((
                (
                    Statement::LetBinding((new_pat, pat.1.clone()), typ, new_e),
                    s_span,
                ),
                name_context,
            ))
        }
    }
}

fn resolve_block(
    sess: &Session,
    (b, b_span): Spanned<Block>,
    name_context: &NameContext,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Block>> {
    let mut new_stmts = Vec::new();
    let mut name_context = name_context.clone();
    for s in b.stmts.into_iter() {
        let (new_stmt, new_name_context) = resolve_statement(sess, s, name_context, top_level_ctx)?;
        new_stmts.push(new_stmt);
        name_context = new_name_context;
    }
    Ok((
        Block {
            stmts: new_stmts,
            mutated: None,
            return_typ: None,
        },
        b_span,
    ))
}

fn resolve_item(
    sess: &Session,
    (i, i_span): Spanned<Item>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Item>> {
    match i {
        Item::ConstDecl(id, typ, e) => {
            let new_e = resolve_expression(sess, e, &HashMap::new(), top_level_ctx)?;
            Ok((Item::ConstDecl(id, typ, new_e), i_span))
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = resolve_expression(sess, size, &HashMap::new(), top_level_ctx)?;
            Ok((Item::ArrayDecl(id, new_size, cell_t, index_typ), i_span))
        }
        Item::NaturalIntegerDecl(typ_ident, canvas_typ_ident, secrecy, canvas_size, mod_string) => {
            let new_canvas_size =
                resolve_expression(sess, canvas_size, &HashMap::new(), top_level_ctx)?;
            Ok((
                Item::NaturalIntegerDecl(
                    typ_ident,
                    canvas_typ_ident,
                    secrecy,
                    new_canvas_size,
                    mod_string,
                ),
                i_span,
            ))
        }
        Item::SimplifiedNaturalIntegerDecl(typ_ident, secrecy, canvas_size) => {
            let new_canvas_size =
                resolve_expression(sess, canvas_size, &HashMap::new(), top_level_ctx)?;
            Ok((
                Item::SimplifiedNaturalIntegerDecl(typ_ident, secrecy, new_canvas_size),
                i_span,
            ))
        }
        Item::FnDecl((f, f_span), mut sig, (b, b_span)) => {
            let name_context = HashMap::new();
            let (new_sig_args, name_context) = sig.args.iter().fold(
                (Vec::new(), name_context),
                |(mut new_sig_acc, name_context), ((x, x_span), (t, t_span))| {
                    let new_x = match x {
                        Ident::Unresolved(s) => to_fresh_ident(s),
                        _ => panic!("should not happen"),
                    };
                    let name_context = add_name(x, &new_x, name_context);
                    new_sig_acc.push(((new_x, x_span.clone()), (t.clone(), t_span.clone())));
                    (new_sig_acc, name_context)
                },
            );
            sig.args = new_sig_args;
            let new_b = resolve_block(sess, (b, b_span), &name_context, top_level_ctx)?;
            Ok((Item::FnDecl((f, f_span), sig, new_b), i_span))
        }
    }
}

fn process_decl_item(
    sess: &Session,
    (i, i_span): &Spanned<Item>,
    top_level_context: &mut TopLevelContext,
) -> ResolutionResult<()> {
    match i {
        Item::ConstDecl(id, typ, _e) => {
            top_level_context.consts.insert(id.0.clone(), typ.clone());
            Ok(())
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = match &size.0 {
                Expression::Lit(Literal::Usize(u)) => ArraySize::Integer(u.clone()),
                Expression::Named(Ident::Unresolved(s)) => {
                    ArraySize::Ident(TopLevelIdent(s.clone()))
                }
                _ => {
                    sess.span_rustspec_err(
                        size.1.clone(),
                        "expected identifier or integer literal",
                    );
                    return Err(());
                }
            };
            top_level_context.typ_dict.insert(
                id.0.clone(),
                (
                    (
                        (Borrowing::Consumed, id.1.clone()),
                        (
                            BaseTyp::Array((new_size, size.1.clone()), Box::new(cell_t.clone())),
                            id.1.clone(),
                        ),
                    ),
                    DictEntry::Array,
                ),
            );
            match index_typ {
                None => (),
                Some(index_typ) => {
                    top_level_context.typ_dict.insert(
                        index_typ.0.clone(),
                        (
                            (
                                (Borrowing::Consumed, index_typ.1.clone()),
                                (BaseTyp::Usize, index_typ.1.clone()),
                            ),
                            DictEntry::Alias,
                        ),
                    );
                }
            };
            Ok(())
        }
        Item::NaturalIntegerDecl(typ_ident, canvas_typ_ident, secrecy, canvas_size, mod_string) => {
            process_decl_item(
                sess,
                &(
                    Item::ArrayDecl(
                        canvas_typ_ident.clone(),
                        canvas_size.clone(),
                        match secrecy {
                            Secrecy::Secret => (
                                BaseTyp::Named(
                                    (TopLevelIdent("U8".to_string()), canvas_typ_ident.1.clone()),
                                    None,
                                ),
                                canvas_typ_ident.1.clone(),
                            ),
                            Secrecy::Public => (BaseTyp::UInt8, canvas_typ_ident.1.clone()),
                        },
                        None,
                    ),
                    *i_span,
                ),
                top_level_context,
            )?;
            top_level_context.typ_dict.insert(
                typ_ident.0.clone() ,
                (
                    (
                        (Borrowing::Consumed, (typ_ident.1).clone()),
                        (
                            BaseTyp::NaturalInteger(
                                secrecy.clone(),
                                mod_string.clone(),
                                match &canvas_size.0 {
                                    Expression::Lit(Literal::Usize(size)) => {
                                        (size.clone(), (canvas_size.1).clone())
                                    }
                                    _ => {
                                        sess.span_rustspec_err(
                                            (canvas_size.1).clone(), "the size of the natural integer encoding has to be a usize literal"
                                        );
                                        return Err(())
                                    }
                                },
                            ),
                            typ_ident.1.clone(),
                        ),
                    ),
                    DictEntry::NaturalInteger,
                ),
            );
            Ok(())
        }
        Item::SimplifiedNaturalIntegerDecl(typ_ident, secrecy, canvas_size) => {
            top_level_context.typ_dict.insert(
                typ_ident.0.clone(),
                match &canvas_size.0 {
                    Expression::Lit(Literal::Usize(size)) => (
                        (
                            (Borrowing::Consumed, (typ_ident.1).clone()),
                            (
                                BaseTyp::NaturalInteger(
                                    secrecy.clone(),
                                    (String::new(), DUMMY_SP), // TODO: replace with real modulo value
                                    // For now we can leave this empty because
                                    // We don't use it in the typechecker
                                    (size.clone(), (canvas_size.1).clone()),
                                ),
                                typ_ident.1.clone(),
                            ),
                        ),
                        DictEntry::NaturalInteger,
                    ),
                    _ => {
                        sess.span_rustspec_err(
                            (canvas_size.1).clone(),
                            "the size of the natural integer encoding has to be a usize literal",
                        );
                        return Err(());
                    }
                },
            );
            Ok(())
        }
        Item::FnDecl((f, _f_span), sig, _b) => {
            top_level_context
                .functions
                .insert(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
            Ok(())
        }
    }
}

fn enrich_with_external_crates_symbols<F: Fn(&Vec<Spanned<String>>) -> ExternalData>(
    _sess: &Session,
    p: &Program,
    top_level_ctx: &mut TopLevelContext,
    external_data: &F,
) -> ResolutionResult<()> {
    let ExternalData {
        funcs: extern_funcs,
        consts: extern_consts,
        arrays: extern_arrays,
        nat_ints: extern_nat_ints,
        ty_aliases: extern_aliases,
    } = external_data(&p.imported_crates);
    for (alias_name, alias_ty) in extern_aliases {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent(alias_name.clone()),
            (
                (
                    (Borrowing::Consumed, DUMMY_SP),
                    (alias_ty.clone(), DUMMY_SP),
                ),
                DictEntry::Alias,
            ),
        );
    }
    for (alias_name, alias_ty) in &p.ty_aliases {
        top_level_ctx.typ_dict.insert(
            alias_name.0.clone(),
            (
                ((Borrowing::Consumed, alias_ty.1.clone()), alias_ty.clone()),
                DictEntry::Alias,
            ),
        );
    }
    for (array_name, array_typ) in extern_arrays {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent(array_name),
            (
                ((Borrowing::Consumed, DUMMY_SP), (array_typ, DUMMY_SP)),
                DictEntry::Array,
            ),
        );
    }
    for (nat_int_name, nat_int_typ) in extern_nat_ints {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent(nat_int_name),
            (
                ((Borrowing::Consumed, DUMMY_SP), (nat_int_typ, DUMMY_SP)),
                DictEntry::NaturalInteger,
            ),
        );
    }
    for (k, v) in extern_funcs {
        top_level_ctx.functions.insert(
            k.clone(),
            match v {
                Ok(v) => FnValue::External(v.clone()),
                Err(s) => FnValue::ExternalNotInHacspec(s.clone()),
            },
        );
    }
    for (k, v) in extern_consts {
        top_level_ctx.consts.insert(TopLevelIdent(k), (v, DUMMY_SP));
    }
    Ok(())
}

pub fn resolve_crate<F: Fn(&Vec<Spanned<String>>) -> ExternalData>(
    sess: &Session,
    p: Program,
    external_data: &F,
) -> ResolutionResult<(Program, TopLevelContext)> {
    let mut top_level_ctx = TopLevelContext {
        consts: HashMap::new(),
        functions: HashMap::new(),
        typ_dict: HashMap::new(),
    };
    // We do a first pass that collects types and signatures of top-level
    // items
    for item in p.items.iter() {
        process_decl_item(sess, item, &mut top_level_ctx)?;
    }
    enrich_with_external_crates_symbols(sess, &p, &mut top_level_ctx, external_data)?;
    Ok((
        Program {
            items: p.items,
            // check_vec(
            //     p.items
            //         .into_iter()
            //         .map(|i| resolve_item(sess, i, &top_level_ctx))
            //         .collect(),
            // )?,
            imported_crates: p.imported_crates,
            ty_aliases: p.ty_aliases,
        },
        top_level_ctx,
    ))
}
