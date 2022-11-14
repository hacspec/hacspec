use crate::rustspec::*;
use rustc_span::DUMMY_SP;

static ID_COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn fresh_var() -> Ident {
    let id = ID_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    Ident::Local(LocalIdent {
        name: "mvar".to_string(),
        id: id,
        mutable: false,
    })
}

/// Wraps an [expression][Expression] `exp` with a `pure` monadic
/// operation from monad `carrier`.
fn pure(carrier: CarrierTyp, exp: Expression) -> Expression {
    Expression::MonadicLet(carrier, vec![], Box::new((exp, DUMMY_SP.into())), true)
}

/// Wrap `exp` into a `pure` (see function [pure][pure]), but only if
/// `exp` is not a `pure …` already.
fn pure_if_non_monadic(carrier: CarrierTyp, x: Spanned<Expression>) -> Spanned<Expression> {
    match x.0 {
        Expression::MonadicLet(..) => x,
        _ => (pure(carrier, x.0), x.1),
    }
}

/// Rewrites an spanned expression to elminate
/// `Expression::QuestionMark` nodes, introducting
/// `Expression::MonadicLet`.
pub fn eliminate_question_marks_in_expressions(e: &Expression) -> Expression {
    // Whenever a sub-expression is monadic, we push it into the
    // mutable `bindings`. Since monadic nodes
    // [MonadicLet][Expression::MonadicLet] only reflect question
    // marks, we can only be in presence of *one* monad per function.
    let mut bindings: Option<(CarrierTyp, Vec<_>)> = None;
    let mut wrap_pure_node = true;
    let mut elim_sub_expr0 =
        |arg: Expression| match eliminate_question_marks_in_expressions(&arg.clone()).clone() {
            Expression::MonadicLet(carrier, lbs, body, _) => {
                bindings = Some(match bindings.clone() {
                    None => (carrier, lbs.clone()),
                    Some((carrier, prev_lbs)) => (
                        carrier,
                        prev_lbs.iter().chain(lbs.iter()).cloned().collect(),
                    ),
                });
                body.0
            }
            arg => arg,
        };
    let mut elim_sub_expr = |arg: Spanned<Expression>| (elim_sub_expr0(arg.clone().0), arg.1);
    let mut elim_boxed_sub_expr =
        |arg: &Box<Spanned<Expression>>| Box::new(elim_sub_expr(*arg.clone()));
    fn find_monadic_let_carrier<T>(exprs: T) -> Option<CarrierTyp>
    where
        T: Iterator<Item = Expression> + Clone,
    {
        exprs.clone().find_map(|e| match e {
            Expression::MonadicLet(carrier, ..) => Some(carrier),
            _ => None,
        })
    }
    let e = match e {
        Expression::MonadicLet(..) => panic!("Typed ADT should never contains a [MonadicLet] node"),
        Expression::Unary(op, e1, t) => {
            Expression::Unary(op.clone(), elim_boxed_sub_expr(e1), t.clone())
        }
        Expression::Binary(op, e1, e2, t) => Expression::Binary(
            op.clone(),
            elim_boxed_sub_expr(e1),
            elim_boxed_sub_expr(e2),
            t.clone(),
        ),
        Expression::QuestionMark(e1, typ) => {
            let e1 = eliminate_question_marks_in_spanned_expressions(&e1);
            let mv = fresh_var();
            let mv_expr = Box::new((Expression::Named(mv.clone()), DUMMY_SP.into()));
            if let (Expression::MonadicLet(carrier, bindings, body, _), _) = e1 {
                Expression::MonadicLet(
                    carrier,
                    bindings
                        .into_iter()
                        .chain(std::iter::once((mv.clone(), body.clone())))
                        .collect(),
                    mv_expr,
                    false,
                )
            } else {
                Expression::MonadicLet(
                    typ.clone()
                        .expect("[QuestionMark] nodes in typed ADTs should always carry a type"),
                    vec![(mv.clone(), Box::new(e1))],
                    mv_expr,
                    true,
                )
            }
        }
        Expression::FuncCall(prefix, name, args, arg_types) => Expression::FuncCall(
            prefix.clone(),
            name.clone(),
            args.into_iter()
                .cloned()
                .map(|(x, xb)| (elim_sub_expr(x), xb))
                .collect(),
            arg_types.clone(),
        ),
        Expression::MethodCall(self_, self_typ, name, args, arg_types) => {
            let (self_expr, self_span) = *self_.clone();
            Expression::MethodCall(
                Box::new((elim_sub_expr(self_expr), self_span)),
                self_typ.clone(),
                name.clone(),
                args.into_iter()
                    .cloned()
                    .map(|(x, xb)| (elim_sub_expr(x), xb))
                    .collect(),
                arg_types.clone(),
            )
        }
        Expression::EnumInject(t, n, e1) => Expression::EnumInject(
            t.clone(),
            n.clone(),
            e1.as_ref()
                // TODO: Why does EnumInject carries a
                // `Spanned<Box<Expression>>` instead of a
                // `Box<Spanned<Expression>>`?
                .map(|(e, es)| (*e.clone(), es.clone()))
                .map(|e1| elim_sub_expr(e1.clone()))
                .map(|(e, es)| (Box::new(e), es)),
        ),
        Expression::InlineConditional(scrutinee, then_, else_) => {
            let scrutinee = elim_boxed_sub_expr(scrutinee);
            let then_ = eliminate_question_marks_in_spanned_expressions(&*then_.clone());
            let else_ = eliminate_question_marks_in_spanned_expressions(&*else_.clone());
            if let Some(carrier) =
                find_monadic_let_carrier([then_.clone().0, else_.clone().0].iter().cloned())
            {
                wrap_pure_node = false;
                Expression::InlineConditional(
                    scrutinee,
                    Box::new(pure_if_non_monadic(carrier.clone(), then_)),
                    Box::new(pure_if_non_monadic(carrier.clone(), else_)),
                )
            } else {
                Expression::InlineConditional(scrutinee, Box::new(then_), Box::new(else_))
            }
        }
        Expression::MatchWith(scrutinee, branches) => {
            let branches = branches
                .into_iter()
                .cloned()
                .map(|(pat, arm)| (pat, eliminate_question_marks_in_spanned_expressions(&arm)));
            let scrutinee = elim_boxed_sub_expr(scrutinee);
            if let Some(carrier) = find_monadic_let_carrier(branches.clone().map(|(.., (x, _))| x))
            {
                wrap_pure_node = false;
                let def = Box::new((
                    Expression::MatchWith(
                        scrutinee,
                        branches
                            .map(|(pat, arm)| (pat, pure_if_non_monadic(carrier.clone(), arm)))
                            .collect(),
                    ),
                    DUMMY_SP.into(),
                ));
                let mv = fresh_var();
                Expression::MonadicLet(
                    carrier.clone(),
                    vec![(mv.clone(), def)],
                    Box::new((Expression::Named(mv.clone()), DUMMY_SP.into())),
                    true,
                )
            } else {
                Expression::MatchWith(scrutinee, branches.collect())
            }
        }
        Expression::ArrayIndex(n, e1, t) => {
            Expression::ArrayIndex(n.clone(), elim_boxed_sub_expr(e1), t.clone())
        }
        Expression::NewArray(n, t, args) => Expression::NewArray(
            n.clone(),
            t.clone(),
            args.into_iter().cloned().map(elim_sub_expr).collect(),
        ),
        Expression::Tuple(args) => {
            Expression::Tuple(args.into_iter().cloned().map(elim_sub_expr).collect())
        }
        Expression::IntegerCasting(e1, d, o) => {
            Expression::IntegerCasting(elim_boxed_sub_expr(e1), d.clone(), o.clone())
        }
        Expression::Named(_) | Expression::Lit(_) => e.clone(),
    };
    match bindings {
        Some((carrier, bindings)) => Expression::MonadicLet(
            carrier,
            bindings.clone(),
            Box::new((e, DUMMY_SP.into())),
            wrap_pure_node,
        ),
        _ => e,
    }
}
pub fn eliminate_question_marks_in_spanned_expressions(
    e: &Spanned<Expression>,
) -> Spanned<Expression> {
    (eliminate_question_marks_in_expressions(&e.0), e.1.clone())
}
