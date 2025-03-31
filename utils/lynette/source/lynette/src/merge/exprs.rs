use crate::merge::types::*;
use crate::DeghostMode;
use crate::utils::*;
use crate::merge::utils::*;
use crate::merge::merge::*;

use syn_verus::punctuated::Punctuated;

pub(super) fn merge_exprs(expr: &Expr, expr1: &Expr, expr2: &Expr, mode: &DeghostMode) -> Result<Expr, Error> {
    match (expr, expr1, expr2) {
        (Expr::Array(a), Expr::Array(a1), Expr::Array(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Array conflict", || expr.clone())
        }
        (Expr::Assign(a), Expr::Assign(a1), Expr::Assign(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Assign conflict", || expr.clone())
        }
        (Expr::Async(a), Expr::Async(a1), Expr::Async(a2)) => {
            merge_blocks(&a.block.stmts, &a1.block.stmts, &a2.block.stmts, mode).map(|b| {
                Expr::Async(syn_verus::ExprAsync {
                    attrs: a1.attrs.clone(),
                    async_token: a1.async_token.clone(),
                    capture: a1.capture.clone(),
                    block: b,
                })
            })
        }
        (Expr::Await(a), Expr::Await(a1), Expr::Await(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Await conflict", || expr.clone())
        }
        (Expr::Binary(a), Expr::Binary(a1), Expr::Binary(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Binary conflict", || expr.clone())
        }
        (Expr::Block(a), Expr::Block(a1), Expr::Block(a2)) => {
            merge_blocks(&a.block.stmts, &a1.block.stmts, &a2.block.stmts, mode).map(|b| {
                Expr::Block(syn_verus::ExprBlock {
                    attrs: a1.attrs.clone(),
                    label: a1.label.clone(),
                    block: b,
                })
            })
        }
        (Expr::Break(a), Expr::Break(a1), Expr::Break(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Break conflict", || expr.clone())
        }
        (Expr::Call(a), Expr::Call(a1), Expr::Call(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Call conflict", || expr.clone())
        }
        (Expr::Cast(a), Expr::Cast(a1), Expr::Cast(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Cast conflict", || expr.clone())
        }
        (Expr::Closure(a), Expr::Closure(a1), Expr::Closure(a2)) => {
            let new_requires = merge_requires(&a1.requires, &a2.requires, mode)?;
            let new_ensures = merge_ensures(&a1.ensures, &a2.ensures, mode)?;

            merge_exprs(&a.body, &a1.body, &a2.body, mode).map(|b| {
                Expr::Closure(syn_verus::ExprClosure {
                    requires: new_requires,
                    ensures: new_ensures,
                    body: Box::new(b),
                    ..a1.clone()
                })
            })
        }
        (Expr::Continue(a), Expr::Continue(a1), Expr::Continue(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Continue conflict", || expr.clone())
        }
        (Expr::Field(a), Expr::Field(a1), Expr::Field(a2)) => {
            eq_or_conflict_3(a, a1, a2, "Field conflict", || expr.clone())
        }
        (Expr::ForLoop(l), Expr::ForLoop(l1), Expr::ForLoop(l2)) => {
            let new_decreases = merge_decreases(&l1.decreases, &l2.decreases, mode)?;
            let new_invariant = merge_invariants(&l1.invariant, &l2.invariant, mode)?;

            merge_blocks(&l.body.stmts, &l1.body.stmts, &l2.body.stmts, mode).map(|b| {
                Expr::ForLoop(syn_verus::ExprForLoop {
                    attrs: l1.attrs.clone(),
                    label: l1.label.clone(),
                    for_token: l1.for_token.clone(),
                    pat: l1.pat.clone(),
                    in_token: l1.in_token.clone(),
                    expr_name: l1.expr_name.clone(),
                    expr: l1.expr.clone(), // TODO: Should we also merge this???
                    invariant: new_invariant,
                    decreases: new_decreases,
                    body: b,
                })
            })
        }
        (Expr::Group(a), Expr::Group(a1), Expr::Group(a2)) => {
            merge_exprs(&a.expr, &a1.expr, &a2.expr, mode).map(|e| {
                Expr::Group(syn_verus::ExprGroup {
                    attrs: a1.attrs.clone(),
                    group_token: a1.group_token.clone(),
                    expr: Box::new(e),
                })
            })
        }
        (Expr::If(i), Expr::If(i1), Expr::If(i2)) => {
            merge_exprs(&*i.cond, &i1.cond, &i2.cond, mode).and_then(|new_cond| {
                merge_blocks(
                    &i.then_branch.stmts,
                    &i1.then_branch.stmts,
                    &i2.then_branch.stmts,
                    mode,
                )
                .and_then(|new_then| {
                    match (i.else_branch.as_ref(), i1.else_branch.as_ref(), i2.else_branch.as_ref())
                    {
                        (Some((t1, e)), Some((_, e1)), Some((_, e2))) => {
                            merge_exprs(&*e, &*e1, &*e2, mode).map(|new_else| {
                                Expr::If(syn_verus::ExprIf {
                                    attrs: i1.attrs.clone(),
                                    if_token: i1.if_token.clone(),
                                    cond: Box::new(new_cond),
                                    then_branch: new_then,
                                    else_branch: Some((t1.clone(), Box::new(new_else))),
                                })
                            })
                        }
                        (None, None, None) => Ok(Expr::If(syn_verus::ExprIf {
                            attrs: i1.attrs.clone(),
                            if_token: i1.if_token.clone(),
                            cond: Box::new(new_cond),
                            then_branch: new_then,
                            else_branch: None,
                        })),
                        _ => Err(Error::Conflict(String::from("If-else conflict"))),
                    }
                })
            })
        }
        (Expr::Index(a), Expr::Index(a1), Expr::Index(a2)) => {
            merge_exprs(&a.expr, &a1.expr, &a2.expr, mode).and_then(|new_expr| {
                merge_exprs(&a.index, &a1.index, &a2.index, mode).map(|new_index| {
                    Expr::Index(syn_verus::ExprIndex {
                        attrs: a1.attrs.clone(),
                        expr: Box::new(new_expr),
                        bracket_token: a1.bracket_token.clone(),
                        index: Box::new(new_index),
                    })
                })
            })
        }
        (Expr::Let(l), Expr::Let(l1), Expr::Let(l2)) => {
            merge_exprs(&*l.expr, &*l1.expr, &*l2.expr, mode).and_then(|new_expr| {
                Ok(Expr::Let(syn_verus::ExprLet {
                    attrs: l1.attrs.clone(),
                    let_token: l1.let_token.clone(),
                    pat: l1.pat.clone(),
                    eq_token: l1.eq_token.clone(),
                    expr: Box::new(new_expr),
                }))
            })
        }
        (Expr::Lit(l), Expr::Lit(l1), Expr::Lit(l2)) => {
            eq_or_conflict_3(l, l1, l2, "Lit conflict", || expr.clone())
        }
        (Expr::Loop(l), Expr::Loop(l1), Expr::Loop(l2)) => {
            let new_ieb = merge_invariant_except_breaks(
                &l1.invariant_except_break,
                &l2.invariant_except_break,
                mode,
            )?;
            let new_invariant = merge_invariants(&l1.invariant, &l2.invariant, mode)?;
            let new_invariant_ensures =
                merge_invariant_ensures(&l1.invariant_ensures, &l2.invariant_ensures, mode)?;
            let new_ensures = merge_ensures(&l1.ensures, &l2.ensures, mode)?;
            let new_decreases = merge_decreases(&l1.decreases, &l2.decreases, mode)?;

            merge_blocks(&l.body.stmts, &l1.body.stmts, &l2.body.stmts, mode).map(|b| {
                Expr::Loop(syn_verus::ExprLoop {
                    attrs: l1.attrs.clone(),
                    label: l1.label.clone(),
                    loop_token: l1.loop_token.clone(),
                    body: b,
                    invariant_except_break: new_ieb,
                    invariant: new_invariant,
                    invariant_ensures: new_invariant_ensures,
                    ensures: new_ensures,
                    decreases: new_decreases,
                })
            })
        }
        (Expr::Macro(m), Expr::Macro(m1), Expr::Macro(m2)) => {
            eq_or_conflict_3(m, m1, m2, "Macro conflict", || expr.clone())
        }
        (Expr::Match(m), Expr::Match(m1), Expr::Match(m2)) => {
            merge_exprs(&m.expr, &m1.expr, &m2.expr, mode).and_then(|new_expr| {
                assert!(m.arms.len() == m1.arms.len() && m.arms.len() == m2.arms.len());

                let mut new_arms = Vec::new();

                for i in 0..m.arms.len() {
                    // Pattern and guard should be identical
                    assert!(m.arms[i].pat == m1.arms[i].pat && m.arms[i].pat == m2.arms[i].pat);
                    assert!(
                        m.arms[i].guard == m1.arms[i].guard && m.arms[i].guard == m2.arms[i].guard
                    );

                    new_arms.push(syn_verus::Arm {
                        attrs: m1.arms[i].attrs.clone(),
                        pat: m1.arms[i].pat.clone(),
                        guard: m1.arms[i].guard.clone(),
                        fat_arrow_token: m1.arms[i].fat_arrow_token.clone(),
                        body: Box::new(merge_exprs(
                            &*m.arms[i].body,
                            &*m1.arms[i].body,
                            &*m2.arms[i].body,
                            mode,
                        )?),
                        comma: m1.arms[i].comma.clone(),
                    })
                }

                Ok(Expr::Match(syn_verus::ExprMatch {
                    attrs: m1.attrs.clone(),
                    match_token: m1.match_token.clone(),
                    expr: Box::new(new_expr),
                    brace_token: m1.brace_token.clone(),
                    arms: new_arms,
                }))
            })
        }
        (Expr::MethodCall(c), Expr::MethodCall(c1), Expr::MethodCall(c2)) => {
            // The arguments can be closures which may contain ghost code
            assert!(c.args.len() == c1.args.len() && c.args.len() == c2.args.len());
            let mut new_args = Punctuated::new();

            for i in 0..c.args.len() {
                new_args.push(merge_exprs(&c.args[i], &c1.args[i], &c2.args[i], mode)?);
                new_args.push_punct(syn_verus::token::Comma::default());
            }

            Ok(Expr::MethodCall(syn_verus::ExprMethodCall {
                attrs: c1.attrs.clone(),
                receiver: c1.receiver.clone(),
                dot_token: c1.dot_token.clone(),
                method: c1.method.clone(),
                turbofish: c1.turbofish.clone(),
                paren_token: c1.paren_token.clone(),
                args: new_args,
            }))
        }
        (Expr::Paren(p), Expr::Paren(p1), Expr::Paren(p2)) => {
            merge_exprs(&p.expr, &p1.expr, &p2.expr, mode).map(|e| {
                Expr::Paren(syn_verus::ExprParen {
                    attrs: p1.attrs.clone(),
                    paren_token: p1.paren_token.clone(),
                    expr: Box::new(e),
                })
            })
        }
        (Expr::Path(p), Expr::Path(p1), Expr::Path(p2)) => {
            eq_or_conflict_3(p, p1, p2, "Path conflict", || expr.clone())
        }
        (Expr::Range(r), Expr::Range(r1), Expr::Range(r2)) => {
            eq_or_conflict_3(r, r1, r2, "Range conflict", || expr.clone())
        }
        (Expr::Reference(r), Expr::Reference(r1), Expr::Reference(r2)) => {
            eq_or_conflict_3(r, r1, r2, "Reference conflict", || expr.clone())
        }
        (Expr::Repeat(r), Expr::Repeat(r1), Expr::Repeat(r2)) => {
            eq_or_conflict_3(r, r1, r2, "Repeat conflict", || expr.clone())
        }
        (Expr::Return(r), Expr::Return(r1), Expr::Return(r2)) => {
            match (r.expr.as_ref(), r1.expr.as_ref(), r2.expr.as_ref()) {
                (Some(e), Some(e1), Some(e2)) => merge_exprs(e, e1, e2, mode).map(|new_expr| {
                    Expr::Return(syn_verus::ExprReturn {
                        attrs: r1.attrs.clone(),
                        return_token: r1.return_token.clone(),
                        expr: Some(Box::new(new_expr)),
                    })
                }),
                (None, None, None) => Ok(Expr::Return(r.clone())),
                _ => Err(Error::Conflict(String::from("Return conflict"))),
            }
        }
        (Expr::Struct(s), Expr::Struct(s1), Expr::Struct(s2)) => {
            eq_or_conflict_3(s, s1, s2, "Struct conflict", || expr.clone())
        }
        (Expr::Try(t), Expr::Try(t1), Expr::Try(t2)) => Ok(Expr::Try(syn_verus::ExprTry {
            attrs: t1.attrs.clone(),
            question_token: t1.question_token.clone(),
            expr: Box::new(merge_exprs(&*t.expr, &*t1.expr, &*t2.expr, mode)?),
        })),
        (Expr::TryBlock(t), Expr::TryBlock(t1), Expr::TryBlock(t2)) => {
            merge_blocks(&t.block.stmts, &t1.block.stmts, &t2.block.stmts, mode).map(|b| {
                Expr::TryBlock(syn_verus::ExprTryBlock {
                    attrs: t1.attrs.clone(),
                    try_token: t1.try_token.clone(),
                    block: b,
                })
            })
        }
        (Expr::Tuple(t), Expr::Tuple(t1), Expr::Tuple(t2)) => {
            assert!(t.elems.len() == t1.elems.len() && t.elems.len() == t2.elems.len());

            let mut new_elems = Punctuated::new();
            for i in 0..t.elems.len() {
                new_elems.push(merge_exprs(&t.elems[i], &t1.elems[i], &t2.elems[i], mode)?);
                new_elems.push_punct(syn_verus::token::Comma::default());
            }

            Ok(Expr::Tuple(syn_verus::ExprTuple {
                attrs: t1.attrs.clone(),
                paren_token: t1.paren_token.clone(),
                elems: new_elems,
            }))
        }
        (Expr::Unary(u), Expr::Unary(u1), Expr::Unary(u2)) => {
            merge_exprs(&*u.expr, &*u1.expr, &*u2.expr, mode).map(|e| {
                Expr::Unary(syn_verus::ExprUnary {
                    attrs: u1.attrs.clone(),
                    op: u1.op.clone(),
                    expr: Box::new(e),
                })
            })
        }
        (Expr::Unsafe(u), Expr::Unsafe(u1), Expr::Unsafe(u2)) => {
            // Skip unsafe
            eq_or_conflict_3(u, u1, u2, "Unsafe conflict", || expr.clone())
        }
        (Expr::While(w), Expr::While(w1), Expr::While(w2)) => {
            let new_ieb = merge_invariant_except_breaks(
                &w1.invariant_except_break,
                &w2.invariant_except_break,
                mode,
            )?;
            let new_invariant = merge_invariants(&w1.invariant, &w2.invariant, mode)?;
            let new_invation_ensures =
                merge_invariant_ensures(&w1.invariant_ensures, &w2.invariant_ensures, mode)?;
            let new_ensures = merge_ensures(&w1.ensures, &w2.ensures, mode)?;
            let new_decreases = merge_decreases(&w1.decreases, &w2.decreases, mode)?;

            let new_cond = merge_exprs(&*w.cond, &*w1.cond, &*w2.cond, mode)?;

            merge_blocks(&w.body.stmts, &w1.body.stmts, &w2.body.stmts, mode).map(|b| {
                Expr::While(syn_verus::ExprWhile {
                    attrs: w1.attrs.clone(),
                    label: w1.label.clone(),
                    while_token: w1.while_token.clone(),
                    cond: Box::new(new_cond),
                    body: b,
                    invariant_except_break: new_ieb,
                    invariant: new_invariant,
                    invariant_ensures: new_invation_ensures,
                    ensures: new_ensures,
                    decreases: new_decreases,
                })
            })
        }
        (Expr::Yield(y), Expr::Yield(y1), Expr::Yield(y2)) => {
            match (y.expr.as_ref(), y1.expr.as_ref(), y2.expr.as_ref()) {
                (Some(e), Some(e1), Some(e2)) => merge_exprs(e, e1, e2, mode).map(|new_expr| {
                    Expr::Yield(syn_verus::ExprYield {
                        attrs: y1.attrs.clone(),
                        yield_token: y1.yield_token.clone(),
                        expr: Some(Box::new(new_expr)),
                    })
                }),
                (None, None, None) => Ok(Expr::Yield(y.clone())),
                _ => Err(Error::Conflict(String::from("Yield conflict"))),
            }
        }
        _ => Err(Error::Conflict(String::from("Expr type conflict"))),
    }
}