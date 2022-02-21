use std::fmt;

use im::{HashMap, HashSet};
use rustc_session::Session;

use crate::hir_to_rustspec::ExternalData;
use crate::rustspec::*;
use crate::util::check_vec;
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
    Enum,
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
                let x_tl = TopLevelIdent {
                    string: name.clone(),
                    kind: TopLevelIdentKind::Constant,
                };
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
    sess: &Session,
    (e, e_span): Spanned<Expression>,
    name_context: &NameContext,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Expression>> {
    match e {
        Expression::Unary(op, e1, ty) => {
            let new_e1 = resolve_expression(sess, *e1, name_context, top_level_ctx)?;
            Ok((Expression::Unary(op, Box::new(new_e1), ty), e_span))
        }
        Expression::Binary(op, e1, e2, ty) => {
            let new_e1 = resolve_expression(sess, *e1, name_context, top_level_ctx)?;
            let new_e2 = resolve_expression(sess, *e2, name_context, top_level_ctx)?;
            Ok((
                Expression::Binary(op, Box::new(new_e1), Box::new(new_e2), ty),
                e_span,
            ))
        }
        Expression::MatchWith(arg, arms) => {
            let new_arg = resolve_expression(sess, *arg, name_context, top_level_ctx)?;
            let new_arms = check_vec(
                arms.into_iter()
                    .map(|(enum_name, case_name, payload, arm)| {
                        let (new_payload, new_name_context) = match payload {
                            None => (None, name_context.clone()),
                            Some(payload) => {
                                let (new_pat, new_name_context) =
                                    resolve_pattern(sess, &payload, top_level_ctx)?;
                                (Some((new_pat, payload.1.clone())), new_name_context)
                            }
                        };
                        let name_context = new_name_context.union(name_context.clone());
                        let new_arm = resolve_expression(sess, arm, &name_context, top_level_ctx)?;
                        Ok((enum_name, case_name, new_payload, new_arm))
                    })
                    .collect(),
            )?;
            Ok((Expression::MatchWith(Box::new(new_arg), new_arms), e_span))
        }
        Expression::EnumInject(enum_name, case_name, payload) => Ok((
            Expression::EnumInject(
                enum_name,
                case_name,
                match payload {
                    None => None,
                    Some(payload) => {
                        let (new_payload, new_payload_span) = resolve_expression(
                            sess,
                            (*payload.0, payload.1),
                            &name_context,
                            top_level_ctx,
                        )?;
                        Some((Box::new(new_payload), new_payload_span))
                    }
                },
            ),
            e_span,
        )),
        Expression::InlineConditional(e1, e2, e3) => {
            let new_e1 = resolve_expression(sess, *e1, name_context, top_level_ctx)?;
            let new_e2 = resolve_expression(sess, *e2, name_context, top_level_ctx)?;
            let new_e3 = resolve_expression(sess, *e3, name_context, top_level_ctx)?;
            Ok((
                Expression::InlineConditional(Box::new(new_e1), Box::new(new_e2), Box::new(new_e3)),
                e_span,
            ))
        }
        Expression::Named(i) => {
            let new_i = find_ident(
                sess,
                &(i.clone(), e_span.clone()),
                name_context,
                top_level_ctx,
            )?;
            Ok((Expression::Named(new_i), e_span))
        }
        Expression::FuncCall(ty, f, args) => {
            let new_args = check_vec(
                args.into_iter()
                    .map(|arg| {
                        let new_arg0 =
                            resolve_expression(sess, arg.0, name_context, top_level_ctx)?;
                        Ok((new_arg0, arg.1))
                    })
                    .collect(),
            )?;
            Ok((Expression::FuncCall(ty, f, new_args), e_span))
        }
        Expression::MethodCall(self_, ty, f, args) => {
            let (self_, self_borrow) = *self_;
            let new_self = resolve_expression(sess, self_, name_context, top_level_ctx)?;
            let new_args = check_vec(
                args.into_iter()
                    .map(|arg| {
                        let new_arg0 =
                            resolve_expression(sess, arg.0, name_context, top_level_ctx)?;
                        Ok((new_arg0, arg.1))
                    })
                    .collect(),
            )?;
            Ok((
                Expression::MethodCall(Box::new((new_self, self_borrow)), ty, f, new_args),
                e_span,
            ))
        }
        Expression::Lit(_) => Ok((e, e_span)),
        Expression::ArrayIndex(x, e1, typ) => {
            let new_x = find_ident(sess, &x, name_context, top_level_ctx)?;
            let new_e1 = resolve_expression(sess, *e1, name_context, top_level_ctx)?;
            Ok((
                Expression::ArrayIndex((new_x, x.1), Box::new(new_e1), typ),
                e_span,
            ))
        }
        Expression::NewArray(x, ty, args) => {
            let new_args = check_vec(
                args.into_iter()
                    .map(|arg| resolve_expression(sess, arg, name_context, top_level_ctx))
                    .collect(),
            )?;
            Ok((Expression::NewArray(x, ty, new_args), e_span))
        }
        Expression::Tuple(args) => {
            let new_args = check_vec(
                args.into_iter()
                    .map(|arg| resolve_expression(sess, arg, name_context, top_level_ctx))
                    .collect(),
            )?;
            Ok((Expression::Tuple(new_args), e_span))
        }
        Expression::IntegerCasting(e1, from, to) => {
            let new_e1 = resolve_expression(sess, *e1, name_context, top_level_ctx)?;
            Ok((
                Expression::IntegerCasting(Box::new(new_e1), from, to),
                e_span,
            ))
        }
    }
}

fn resolve_pattern(
    sess: &Session,
    (pat, _pat_span): &Spanned<Pattern>,
    top_ctx: &TopLevelContext,
) -> ResolutionResult<(Pattern, NameContext)> {
    match pat {
        Pattern::SingleCaseEnum(name, inner_pat) => {
            let (new_inner_pat, sub_context) = resolve_pattern(sess, &*inner_pat, top_ctx)?;
            Ok((
                Pattern::SingleCaseEnum(
                    name.clone(),
                    Box::new((new_inner_pat, inner_pat.1.clone())),
                ),
                sub_context,
            ))
        }
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
        Statement::ForLoop(None, lower, upper, body) => {
            let new_lower = resolve_expression(sess, lower, &name_context, top_level_ctx)?;
            let new_upper = resolve_expression(sess, upper, &name_context, top_level_ctx)?;
            let new_body = resolve_block(sess, body, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::ForLoop(None, new_lower, new_upper, new_body),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::ForLoop(Some((var, var_span)), lower, upper, body) => {
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
                    Statement::ForLoop(Some((new_var, var_span)), new_lower, new_upper, new_body),
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
        Statement::ArrayUpdate(var, index, e, question_mark, typ) => {
            let new_var = find_ident(sess, &var, &name_context, top_level_ctx)?;
            let new_index = resolve_expression(sess, index, &name_context, top_level_ctx)?;
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::ArrayUpdate(
                        (new_var, var.1.clone()),
                        new_index,
                        new_e,
                        question_mark,
                        typ,
                    ),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::Reassignment(var, e, question_mark) => {
            let new_var = find_ident(sess, &var, &name_context, top_level_ctx)?;
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            Ok((
                (
                    Statement::Reassignment((new_var, var.1.clone()), new_e, question_mark),
                    s_span,
                ),
                name_context,
            ))
        }
        Statement::LetBinding(pat, typ, e, question_mark) => {
            let new_e = resolve_expression(sess, e, &name_context, top_level_ctx)?;
            let (new_pat, new_name_context) = resolve_pattern(sess, &pat, top_level_ctx)?;
            let name_context = new_name_context.union(name_context);
            Ok((
                (
                    Statement::LetBinding((new_pat, pat.1.clone()), typ, new_e, question_mark),
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
            contains_question_mark: None,
        },
        b_span,
    ))
}

fn resolve_item(
    sess: &Session,
    (item, i_span): Spanned<DecoratedItem>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<DecoratedItem>> {
    let i = item.clone().item;
    let i = match i {
        Item::ConstDecl(id, typ, e) => {
            let new_e = resolve_expression(sess, e, &HashMap::new(), top_level_ctx)?;
            Ok((Item::ConstDecl(id, typ, new_e), i_span))
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = resolve_expression(sess, size, &HashMap::new(), top_level_ctx)?;
            Ok((Item::ArrayDecl(id, new_size, cell_t, index_typ), i_span))
        }
        Item::EnumDecl(_, _) | Item::AliasDecl(_, _) | Item::ImportedCrate(_) => Ok((i, i_span)),
        Item::NaturalIntegerDecl(typ_ident, secrecy, canvas_size, info) => {
            let new_canvas_size =
                resolve_expression(sess, canvas_size, &HashMap::new(), top_level_ctx)?;
            Ok((
                Item::NaturalIntegerDecl(typ_ident, secrecy, new_canvas_size, info),
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
    };
    match i {
        Ok((i, i_span)) => Ok((
            DecoratedItem {
                item: i,
                tags: item.tags,
            },
            i_span,
        )),
        Err(a) => Err(a),
    }
}

fn process_decl_item(
    sess: &Session,
    (i, i_span): &Spanned<DecoratedItem>,
    top_level_context: &mut TopLevelContext,
) -> ResolutionResult<()> {
    match &i.item {
        Item::ConstDecl(id, typ, _e) => {
            top_level_context.consts.insert(id.0.clone(), typ.clone());
            Ok(())
        }
        Item::EnumDecl(name, cases) => {
            top_level_context.typ_dict.insert(
                name.0.clone(),
                (
                    (
                        (Borrowing::Consumed, i_span.clone()),
                        (BaseTyp::Enum(cases.clone(), Vec::new()), i_span.clone()),
                    ),
                    DictEntry::Enum,
                ),
            );
            Ok(())
        }
        Item::ArrayDecl(id, size, cell_t, index_typ) => {
            let new_size = match &size.0 {
                Expression::Lit(Literal::Usize(u)) => ArraySize::Integer(u.clone()),
                Expression::Named(Ident::Unresolved(s)) => ArraySize::Ident(TopLevelIdent {
                    string: s.clone(),
                    kind: TopLevelIdentKind::Constant,
                }),
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
        Item::NaturalIntegerDecl(typ_ident, secrecy, canvas_size, info) => {
            let mod_string = match info {
                Some((canvas_typ_ident, mod_string)) => {
                    process_decl_item(
                        sess,
                        &(
                            DecoratedItem {
                                item: Item::ArrayDecl(
                                    canvas_typ_ident.clone(),
                                    canvas_size.clone(),
                                    match secrecy {
                                        Secrecy::Secret => (
                                            BaseTyp::Named(
                                                (U8_TYP(), canvas_typ_ident.1.clone()),
                                                None,
                                            ),
                                            canvas_typ_ident.1.clone(),
                                        ),
                                        Secrecy::Public => {
                                            (BaseTyp::UInt8, canvas_typ_ident.1.clone())
                                        }
                                    },
                                    None,
                                ),
                                tags: ItemTagSet(HashSet::unit("code".to_string())),
                            },
                            *i_span,
                        ),
                        top_level_context,
                    )?;
                    mod_string.clone()
                }
                None => (String::new(), DUMMY_SP.into()), // TODO: replace with real modulo value
                                                          // For now we can leave this empty because
                                                          // We don't use it in the typechecker
            };
            top_level_context.typ_dict.insert(
                typ_ident.0.clone() ,
                (
                    (
                        (Borrowing::Consumed, (typ_ident.1).clone()),
                        (
                            BaseTyp::NaturalInteger(
                                secrecy.clone(),
                                mod_string,
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
        Item::AliasDecl(alias_name, alias_ty) => {
            top_level_context.typ_dict.insert(
                alias_name.0.clone(),
                (
                    ((Borrowing::Consumed, alias_ty.1.clone()), alias_ty.clone()),
                    DictEntry::Alias,
                ),
            );
            Ok(())
        }
        Item::ImportedCrate(_) => {
            // Foreign items already imported at this point
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

pub fn get_imported_crates(p: &Program) -> Vec<Spanned<String>> {
    p.items
        .iter()
        .map(|i| ((&i.0.item), &i.1))
        .filter(|i| match &i.0 {
            Item::ImportedCrate(_) => true,
            _ => false,
        })
        .map(|i| match &i.0 {
            Item::ImportedCrate((
                TopLevelIdent {
                    string: s,
                    kind: TopLevelIdentKind::Crate,
                },
                _,
            )) => (s.clone(), i.1.clone()),
            _ => panic!("should not happen"),
        })
        .collect()
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
        enums: extern_enums,
        ty_aliases: extern_aliases,
    } = external_data(&get_imported_crates(p));
    for (alias_name, alias_ty) in extern_aliases {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent {
                string: alias_name.clone(),
                kind: TopLevelIdentKind::Type,
            },
            (
                (
                    (Borrowing::Consumed, DUMMY_SP.into()),
                    (alias_ty.clone(), DUMMY_SP.into()),
                ),
                DictEntry::Alias,
            ),
        );
    }
    for (array_name, array_typ) in extern_arrays {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent {
                string: array_name,
                kind: TopLevelIdentKind::Type,
            },
            (
                (
                    (Borrowing::Consumed, DUMMY_SP.into()),
                    (array_typ, DUMMY_SP.into()),
                ),
                DictEntry::Array,
            ),
        );
    }
    for (enum_name, enum_typ) in extern_enums {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent {
                string: enum_name,
                kind: TopLevelIdentKind::Type,
            },
            (
                (
                    (Borrowing::Consumed, DUMMY_SP.into()),
                    (enum_typ, DUMMY_SP.into()),
                ),
                DictEntry::Enum,
            ),
        );
    }
    for (nat_int_name, nat_int_typ) in extern_nat_ints {
        top_level_ctx.typ_dict.insert(
            TopLevelIdent {
                string: nat_int_name,
                kind: TopLevelIdentKind::Type,
            },
            (
                (
                    (Borrowing::Consumed, DUMMY_SP.into()),
                    (nat_int_typ, DUMMY_SP.into()),
                ),
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
        top_level_ctx.consts.insert(
            TopLevelIdent {
                string: k,
                kind: TopLevelIdentKind::Constant,
            },
            (v, DUMMY_SP.into()),
        );
    }
    Ok(())
}

pub fn resolve_crate<F: Fn(&Vec<Spanned<String>>) -> ExternalData>(
    sess: &Session,
    p: Program,
    external_data: &F,
    top_level_ctx : &mut TopLevelContext,
) -> ResolutionResult<Program> {
    // First we fill the context with external symbols
    enrich_with_external_crates_symbols(sess, &p, top_level_ctx, external_data)?;
    // Then we do a first pass that collects types and signatures of top-level
    // items
    for item in p.items.iter() {
        process_decl_item(sess, item, top_level_ctx)?;
    }
    // And finally a second pass that performs the actual name resolution
    Ok(
        Program {
            items: check_vec(
                p.items
                    .into_iter()
                    .map(|i| resolve_item(sess, i, &top_level_ctx))
                    .collect(),
            )?,
        }
    )
}
