use im::{HashMap, HashSet};
use rustc_session::Session;

use crate::rustspec::*;
use crate::util::check_vec;
use std::{
    ops::Add,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::name_resolution::{FnKey, FnValue, TopLevelContext};

pub static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_hacspec_id() -> usize {
    ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

pub(crate) fn to_fresh_ident(x: &String, mutable: bool) -> Ident {
    Ident::Local(LocalIdent {
        id: fresh_hacspec_id(),
        name: x.clone(),
        mutable,
    })
}

pub type ResolutionResult<T> = Result<T, ()>;

#[derive(Clone, Debug)]
pub struct ScopeMutInfo {
    pub funcs: FunctionDependencies,
}
impl ScopeMutInfo {
    fn new() -> Self {
        ScopeMutInfo {
            funcs: FunctionDependencies(HashSet::new()),
        }
    }

    fn extend(&mut self, s: ScopeMutInfo) {
        self.funcs.0.extend(s.funcs.0);
    }

    fn extend_with_block(&mut self, b: Block) {
        self.funcs.0.extend(b.function_dependencies.0);
    }
}

fn resolve_expression(
    sess: &Session,
    (e, e_span): Spanned<Expression>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<ScopeMutInfo> {
    log::trace!("resolve_expression ({:?}, {:?})", e, e_span);
    match e {
        Expression::Unary(_, e1, _) => {
            let smi_new_e1 = resolve_expression(sess, *e1, top_level_ctx)?;
            Ok(smi_new_e1)
        }
        Expression::Binary(_, e1, e2, _) => {
            let smi_new_e1 = resolve_expression(sess, *e1, top_level_ctx)?;
            let smi_new_e2 = resolve_expression(sess, *e2, top_level_ctx)?;
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_e1);
            smi.extend(smi_new_e2);
            Ok(smi)
        }
        Expression::MonadicLet(..) =>
        // TODO: eliminiate this `panic!` with nicer types (See issue #303)
        {
            panic!(
                "The name resolution phase expects an AST free of [Expression::MonadicLet] node."
            )
        }
        Expression::QuestionMark(e, _) => {
            let smi_new_e = resolve_expression(sess, *e, top_level_ctx)?;
            Ok(smi_new_e)
        }
        Expression::MatchWith(arg, arms) => {
            let smi_new_arg = resolve_expression(sess, *arg, top_level_ctx)?;
            let smi_new_arms: Vec<_> = check_vec(
                arms.into_iter()
                    .map(|(_, arm)| {
                        let smi_new_arm = resolve_expression(sess, arm, top_level_ctx)?;
                        Ok(smi_new_arm)
                    })
                    .collect(),
            )?;
            let smi_new_arms: ScopeMutInfo =
                smi_new_arms
                    .into_iter()
                    .fold(ScopeMutInfo::new(), |mut smi, x| {
                        smi.extend(x);
                        smi
                    });
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_arg);
            smi.extend(smi_new_arms);
            Ok(smi)
        }
        Expression::FieldAccessor(box e1, _) => {
            let smi = resolve_expression(sess, e1, top_level_ctx)?;
            Ok(smi)
        }
        Expression::EnumInject(_, _, payload) => {
            let smi_payload = match payload {
                None => ScopeMutInfo::new(),
                Some(payload) => {
                    let smi_payload =
                        resolve_expression(sess, (*payload.0, payload.1), top_level_ctx)?;
                    smi_payload
                }
            };
            Ok(smi_payload)
        }
        Expression::InlineConditional(e1, e2, e3) => {
            let smi_new_e1 = resolve_expression(sess, *e1, top_level_ctx)?;
            let smi_new_e2 = resolve_expression(sess, *e2, top_level_ctx)?;
            let smi_new_e3 = resolve_expression(sess, *e3, top_level_ctx)?;
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_e1);
            smi.extend(smi_new_e2);
            smi.extend(smi_new_e3);
            Ok(smi)
        }
        Expression::Named(_) => Ok(ScopeMutInfo::new()),
        Expression::FuncCall(_, f, args, _) => {
            let smi_new_args: Vec<_> = check_vec(
                args.into_iter()
                    .map(|arg| Ok(resolve_expression(sess, arg.0, top_level_ctx)?))
                    .collect(),
            )?;
            let smi_new_args: ScopeMutInfo =
                smi_new_args
                    .into_iter()
                    .fold(ScopeMutInfo::new(), |mut smi, x| {
                        smi.extend(x);
                        smi
                    });

            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_args);
            smi.funcs.0.insert(f.clone().0);
            match top_level_ctx
                .functions
                .get(&FnKey::Independent(f.clone().0))
            {
                Some(FnValue::Local(sig)) => {
                    smi.funcs.0.extend(sig.function_dependencies.clone().0);
                    ()
                }
                _ => (),
            };

            Ok(smi)
        }
        Expression::MethodCall(self_, _, f, args, _) => {
            let (self_, _) = *self_;
            let smi_new_self = resolve_expression(sess, self_, top_level_ctx)?;
            let smi_new_args: Vec<_> = check_vec(
                args.into_iter()
                    .map(|arg| {
                        let smi_new_arg0 = resolve_expression(sess, arg.0, top_level_ctx)?;
                        Ok(smi_new_arg0)
                    })
                    .collect(),
            )?;
            let smi_new_args: ScopeMutInfo =
                smi_new_args
                    .into_iter()
                    .fold(ScopeMutInfo::new(), |mut smi, x| {
                        smi.extend(x);
                        smi
                    });

            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_self);
            smi.extend(smi_new_args);
            smi.funcs.0.insert(f.clone().0);
            match top_level_ctx
                .functions
                .get(&FnKey::Independent(f.clone().0))
            {
                Some(FnValue::Local(sig)) => {
                    smi.funcs.0.extend(sig.function_dependencies.clone().0);
                    ()
                }
                _ => (),
            };

            Ok(smi)
        }
        Expression::Lit(_) => Ok(ScopeMutInfo::new()),
        Expression::ArrayIndex(_, e1, _) => {
            let smi_new_e1 = resolve_expression(sess, *e1, top_level_ctx)?;
            Ok(smi_new_e1)
        }
        Expression::NewArray(_, _, args) => {
            let smi_new_args: Vec<_> = check_vec(
                args.into_iter()
                    .map(|arg| resolve_expression(sess, arg, top_level_ctx))
                    .collect(),
            )?;
            let smi_new_args: ScopeMutInfo =
                smi_new_args
                    .into_iter()
                    .fold(ScopeMutInfo::new(), |mut smi, x| {
                        smi.extend(x);
                        smi
                    });
            Ok(smi_new_args)
        }
        Expression::Tuple(args) => {
            let smi_new_args: Vec<_> = check_vec(
                args.into_iter()
                    .map(|arg| resolve_expression(sess, arg, top_level_ctx))
                    .collect(),
            )?;
            let smi_new_args: ScopeMutInfo =
                smi_new_args
                    .into_iter()
                    .fold(ScopeMutInfo::new(), |mut smi, x| {
                        smi.extend(x);
                        smi
                    });
            Ok(smi_new_args)
        }
        Expression::IntegerCasting(e1, _, _) => {
            let smi_new_e1 = resolve_expression(sess, *e1, top_level_ctx)?;
            Ok(smi_new_e1)
        }
    }
}

fn resolve_statement(
    sess: &Session,
    (s, s_span): Spanned<Statement>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<ScopeMutInfo> {
    log::trace!("resolve_statements ({:?}, {:?})", s, s_span);
    match s {
        Statement::Conditional(cond, then_b, else_b, _) => {
            let smi_new_cond = resolve_expression(sess, cond, top_level_ctx)?;
            let new_then_b = resolve_block(sess, then_b, top_level_ctx)?;
            let smi_new_else_b = match else_b {
                None => ScopeMutInfo::new(),
                Some(else_b) => {
                    let new_else_b = resolve_block(sess, else_b, top_level_ctx)?;
                    let mut smi = ScopeMutInfo::new();
                    smi.extend_with_block(new_else_b.0.clone());
                    smi
                }
            };

            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_cond);
            smi.extend_with_block(new_then_b.0.clone());
            smi.extend(smi_new_else_b);

            Ok(smi)
        }
        Statement::ForLoop(_, lower, upper, body) => {
            let smi_new_lower = resolve_expression(sess, lower, top_level_ctx)?;
            let smi_new_upper = resolve_expression(sess, upper, top_level_ctx)?;
            let new_body = resolve_block(sess, body, top_level_ctx)?;
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_lower);
            smi.extend(smi_new_upper);
            smi.extend_with_block(new_body.clone().0);
            Ok(smi)
        }
        Statement::ReturnExp(e, _) => {
            let smi_new_e = resolve_expression(sess, (e, s_span.clone()), top_level_ctx)?;
            Ok(smi_new_e)
        }
        Statement::ArrayUpdate(_, index, e, _, _, _) => {
            let smi_new_index = resolve_expression(sess, index, top_level_ctx)?;
            let smi_new_e = resolve_expression(sess, e, top_level_ctx)?;
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_index);
            smi.extend(smi_new_e);
            Ok(smi.clone())
        }
        Statement::Reassignment(_, _, e, _, _) => {
            let smi_new_e = resolve_expression(sess, e, top_level_ctx)?;
            Ok(smi_new_e.clone())
        }
        Statement::LetBinding(_, _, e, _, _) => {
            let smi_new_e = resolve_expression(sess, e, top_level_ctx)?;
            let mut smi = ScopeMutInfo::new();
            smi.extend(smi_new_e);
            Ok(smi.clone())
        }
    }
}

fn resolve_block(
    sess: &Session,
    (b, b_span): Spanned<Block>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<Block>> {
    log::trace!("resolve_block ({:#?}, {:#?})", b, b_span);
    let mut smi = ScopeMutInfo::new();
    for s in b.stmts.clone().into_iter() {
        let smi_stmt = resolve_statement(sess, s, top_level_ctx)?;
        println!("smi_stmt {:?}", smi_stmt);
        smi.extend(smi_stmt);
    }
    Ok((
        Block {
            function_dependencies: smi.funcs,
            ..b
        },
        b_span,
    ))
}

fn resolve_item(
    sess: &Session,
    (item, i_span): Spanned<DecoratedItem>,
    top_level_ctx: &TopLevelContext,
) -> ResolutionResult<Spanned<DecoratedItem>> {
    log::trace!("resolve_item ({:?}, {:?})", item, i_span);
    let i = item.clone().item;
    let i = match i {
        Item::FnDecl((f, f_span), mut sig, (b, b_span)) => {
            let new_sig_args =
                sig.args
                    .iter()
                    .fold(Vec::new(), |mut new_sig_acc, ((x, x_span), (t, t_span))| {
                        let new_x = match x {
                            Ident::Unresolved(s) => to_fresh_ident(s, false),
                            s => s.clone(),
                        };
                        new_sig_acc.push(((new_x, x_span.clone()), (t.clone(), t_span.clone())));
                        new_sig_acc
                    });
            sig.args = new_sig_args;
            let new_b = resolve_block(sess, (b, b_span), top_level_ctx)?;
            sig.function_dependencies = new_b.clone().0.function_dependencies;
            Ok((Item::FnDecl((f, f_span), sig, new_b), i_span))
        }
        i => Ok((i, i_span)),
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

pub fn resolve_fun_dep(
    f: FunctionDependency,
    f_dep: FunctionDependencies,
    f_deps_map: HashMap<FunctionDependency, FunctionDependencies>,
) -> FunctionDependencies {
    if f_deps_map.contains_key(&f.clone()) {
        let mut fdeps: FunctionDependencies = f_deps_map[&f.clone()].clone();
        for f_other in f_dep.0 {
            fdeps.0.insert(f_other.clone());
            if f_deps_map.contains_key(&f_other.clone()) {
                for x in resolve_fun_dep(
                    f.clone(),
                    f_deps_map[&f_other.clone()].clone(),
                    f_deps_map.clone(),
                )
                .0
                {
                    fdeps.0.insert(x);
                }
            }
        }
        fdeps
    } else {
        FunctionDependencies(HashSet::new())
    }
}

pub fn resolve_crate(
    sess: &Session,
    p: Program,
    top_level_ctx: &mut TopLevelContext,
) -> ResolutionResult<Program> {
    let mut items = p.items;
    items = check_vec(
        items
            .into_iter()
            .map(|i| resolve_item(sess, i, &top_level_ctx))
            .collect(),
    )?;

    let mut f_deps_map: HashMap<FunctionDependency, FunctionDependencies> = HashMap::new();

    for x in items.clone().into_iter() {
        match x.0.item {
            Item::FnDecl((f, _f_span), sig, _b) => {
                println!("{:?} depends on {:?}", f, sig.function_dependencies);
                f_deps_map.insert(f.clone(), sig.function_dependencies.clone());
            }
            _ => (),
        }
    }

    let items : Vec<Spanned<DecoratedItem>> = items
        .clone()
        .into_iter()
        .map(|x| {
            (
                DecoratedItem {
                    item: match x.0.item {
                        Item::FnDecl((f, f_span), sig, b) => {
                            let sig = FuncSig {
                                function_dependencies: resolve_fun_dep(
                                    f.clone(),
                                    sig.function_dependencies,
                                    f_deps_map.clone(),
                                ),
                                ..sig
                            };
                            top_level_ctx
                                .functions
                                .insert(FnKey::Independent(f.clone()), FnValue::Local(sig.clone()));
                            Item::FnDecl((f.clone(), f_span), sig, b)
                        }
                        i => i.clone(),
                    },
                    ..x.0
                },
                x.1,
            )
        })
        .collect();

    let items = check_vec(
        items.clone()
            .into_iter()
            .map(|i| resolve_item(sess, i, &top_level_ctx))
            .collect(),
    )?;

    Ok(Program { items })
}
