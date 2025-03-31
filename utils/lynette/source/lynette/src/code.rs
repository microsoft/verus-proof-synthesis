use quote::ToTokens;
use serde_json::json;
use std::ops::RangeInclusive;
use std::path::PathBuf;
use std::vec;
use syn::spanned::Spanned;

use crate::deghost::*;
use crate::func::detect_non_linear_assert_expr;
use crate::utils::*;

#[derive(Debug)]
pub enum CallType<'a> {
    Function(&'a syn_verus::ExprCall),
    Method(&'a syn_verus::ExprMethodCall),
}

fn get_calls_expr(expr: &syn_verus::Expr) -> Vec<CallType> {
    match expr {
        syn_verus::Expr::Call(call) => vec![CallType::Function(call)]
            .into_iter()
            .chain(call.args.iter().flat_map(get_calls_expr))
            .collect(),
        syn_verus::Expr::Array(ea) => ea.elems.iter().flat_map(get_calls_expr).collect(),
        syn_verus::Expr::Assign(asg) => {
            // XXX: Can a function call returns a left value?
            get_calls_expr(&asg.right)
        }
        syn_verus::Expr::Async(asy) => asy.block.stmts.iter().flat_map(get_calls_stmt).collect(),
        syn_verus::Expr::Await(aw) => get_calls_expr(&aw.base),
        syn_verus::Expr::Binary(b) => {
            get_calls_expr(&b.left).into_iter().chain(get_calls_expr(&b.right)).collect()
        }
        syn_verus::Expr::Block(bl) => bl.block.stmts.iter().flat_map(get_calls_stmt).collect(),
        syn_verus::Expr::Break(br) => br.expr.as_ref().map_or(vec![], |expr| get_calls_expr(expr)),
        syn_verus::Expr::Const(_) => vec![],
        syn_verus::Expr::Cast(c) => get_calls_expr(&c.expr),
        syn_verus::Expr::Closure(cl) => get_calls_expr(&cl.body),
        syn_verus::Expr::Continue(_) => vec![],
        syn_verus::Expr::Field(f) => get_calls_expr(&f.base),
        syn_verus::Expr::ForLoop(fl) => get_calls_expr(&fl.expr)
            .into_iter()
            .chain(fl.body.stmts.iter().flat_map(get_calls_stmt))
            .collect(),
        syn_verus::Expr::Group(g) => get_calls_expr(&g.expr),
        syn_verus::Expr::If(i) => get_calls_expr(&i.cond)
            .into_iter()
            .chain(i.then_branch.stmts.iter().map(|stmt| get_calls_stmt(stmt)).flatten())
            .chain(i.else_branch.as_ref().map_or(vec![], |(_, eexpr)| get_calls_expr(&*eexpr)))
            .collect(),
        syn_verus::Expr::Index(i) => {
            get_calls_expr(&i.expr).into_iter().chain(get_calls_expr(&i.index)).collect()
        }
        syn_verus::Expr::Infer(_) => vec![],
        syn_verus::Expr::Let(l) => get_calls_expr(&l.expr),
        syn_verus::Expr::Lit(_) => vec![],
        syn_verus::Expr::Loop(l) => l.body.stmts.iter().flat_map(get_calls_stmt).collect(),
        // syn_verus::Expr::Macro(m) => {}
        syn_verus::Expr::Match(m) => get_calls_expr(&m.expr)
            .into_iter()
            .chain(
                m.arms
                    .iter()
                    .map(|arm| {
                        arm.guard
                            .as_ref()
                            .map_or(vec![], |(_, gexpr)| get_calls_expr(&*gexpr))
                            .into_iter()
                            .chain(get_calls_expr(&arm.body))
                    })
                    .flatten(),
            )
            .collect(),
        syn_verus::Expr::MethodCall(m) => {
            let mut calls = get_calls_expr(&m.receiver);
            calls.push(CallType::Method(m));
            calls.into_iter().chain(m.args.iter().flat_map(get_calls_expr)).collect::<Vec<_>>()
        }
        syn_verus::Expr::Paren(p) => get_calls_expr(&p.expr),
        // syn_verus::Expr::Path(p) => {}
        syn_verus::Expr::Range(r) => {
            r.start.as_ref().map_or(vec![], |expr| get_calls_expr(expr))
                .into_iter()
                .chain(r.end.as_ref().map_or(vec![], |expr| get_calls_expr(expr)))
                .collect()
        }
        syn_verus::Expr::RawAddr(r) => get_calls_expr(&r.expr),
        syn_verus::Expr::Reference(r) => get_calls_expr(&r.expr),
        syn_verus::Expr::Repeat(r) => {
            get_calls_expr(&r.expr).into_iter().chain(get_calls_expr(&r.len)).collect()
        }
        syn_verus::Expr::Return(r) => r.expr.as_ref().map_or(vec![], |expr| get_calls_expr(expr)),
        syn_verus::Expr::Struct(s) => s
            .fields
            .iter()
            .flat_map(|field| get_calls_expr(&field.expr))
            .collect::<Vec<_>>()
            .into_iter()
            .chain(s.rest.as_ref().map_or(vec![], |r| get_calls_expr(&*r)))
            .collect(),
        syn_verus::Expr::Try(t) => get_calls_expr(&t.expr),
        syn_verus::Expr::TryBlock(t) => t.block.stmts.iter().flat_map(get_calls_stmt).collect(),
        syn_verus::Expr::Tuple(t) => t.elems.iter().flat_map(get_calls_expr).collect(),
        // syn_verus::Expr::Type(t) => {}
        syn_verus::Expr::Unary(u) => get_calls_expr(&u.expr),
        syn_verus::Expr::Unsafe(_) => {
            // XXX: throw an error?
            vec![]
        }
        // syn_verus::Expr::Verbatim(v) => {}
        syn_verus::Expr::While(w) => get_calls_expr(&w.cond)
            .into_iter()
            .chain(w.body.stmts.iter().flat_map(get_calls_stmt))
            .collect(),
        syn_verus::Expr::Yield(y) => y.expr.as_ref().map_or(vec![], |expr| get_calls_expr(expr)),
        _ => vec![],
    }
}

fn get_calls_stmt(stmt: &syn_verus::Stmt) -> Vec<CallType> {
    match stmt {
        syn_verus::Stmt::Expr(e, _) => get_calls_expr(e),
        syn_verus::Stmt::Local(l) => {
            l.init.as_ref().map_or(vec![], |li| get_calls_expr(&li.expr) )
        }
        syn_verus::Stmt::Item(i) => get_calls_item(i),
        _ => vec![],
    }
}

fn get_calls_item(item: &syn_verus::Item) -> Vec<CallType> {
    match item {
        syn_verus::Item::Fn(f) => f.block.stmts.iter().flat_map(get_calls_stmt).collect(),
        syn_verus::Item::Const(c) => c.expr.as_ref().map_or(vec![], |expr| get_calls_expr(expr)),
        syn_verus::Item::Static(s) => s.expr.as_ref().map_or(vec![], |expr| get_calls_expr(expr)),
        _ => vec![],
    }
}

pub fn get_calls_at(
    filepath: &PathBuf,
    ranges: Option<Vec<RangeInclusive<usize>>>,
) -> Result<Vec<serde_json::Value>, Error> {
    fextract_verus_macro(filepath).and_then(|(files, _)| {
        let mut objs: Vec<serde_json::Value> = Vec::new();

        for file in files {
            let calls = file
                .items
                .iter()
                .flat_map(get_calls_item)
                .filter(|call| {
                    if let Some(ranges) = &ranges {
                        let line = match call {
                            CallType::Function(f) => f.func.span().start().line,
                            CallType::Method(m) => m.method.span().start().line,
                        };

                        ranges.iter().any(|range| range.contains(&line))
                    } else {
                        true
                    }
                })
                .collect::<Vec<_>>();

            for call in calls {
                let ret = match call {
                    CallType::Function(f) => {
                        json!({
                            "func": f.func.to_token_stream().to_string(),
                            "args": arg_list_to_string(&f.args),
                            "line": f.func.span().start().line,
                        })
                    }
                    CallType::Method(m) => {
                        json!({
                            "func": m.method.to_token_stream().to_string(),
                            "args": arg_list_to_string(&m.args),
                            "line": m.method.span().start().line,
                        })
                    }
                };
                objs.push(ret);
            }
        }

        Ok(objs)
    })
}

pub enum Loc {
    Line(usize),
    Offset(usize),
}

fn line_in_span(span: &proc_macro2::Span, line: usize) -> bool {
    span.start().line <= line && span.end().line >= line
}

fn offset_in_span(span: &proc_macro2::Span, offset: usize) -> bool {
    span.byte_range().contains(&offset)
}

fn func_in_range(func: &syn_verus::ItemFn, loc: &Loc) -> bool {
    match loc {
        Loc::Line(l) => line_in_span(&func.block.span(), *l) || line_in_span(&func.sig.span(), *l),
        Loc::Offset(o) => {
            offset_in_span(&func.block.span(), *o) || offset_in_span(&func.sig.span(), *o)
        }
    }
}

fn get_func_at_item(item: &syn_verus::Item, loc: &Loc) -> Option<String> {
    match item {
        syn_verus::Item::Fn(f) => Some(f.sig.ident.to_string()).filter(|_| func_in_range(f, loc)),
        _ => None,
    }
}

pub fn get_func_at(
    filepath: &PathBuf,
    line: Option<usize>,
    offset: Option<usize>,
) -> Result<Vec<String>, Error> {
    fextract_verus_macro(filepath).and_then(|(files, _)| {
        let loc = if let Some(line) = line {
            Loc::Line(line)
        } else if let Some(offset) = offset {
            Loc::Offset(offset)
        } else {
            return Err(Error::NotFound("line or offset".to_string()));
        };

        Ok(files
            .iter()
            .flat_map(|file| &file.items)
            .find_map(|item| get_func_at_item(item, &loc))
            .map_or_else(|| Vec::new(), |func| vec![func]))
    })
}

enum GhostVariant<'a> {
    Assert(&'a syn_verus::Expr),
    AssertForall(&'a syn_verus::Expr),
    Decreases(&'a syn_verus::Expr),
    Ensures(&'a syn_verus::Expr),
    Recommends(&'a syn_verus::Expr),
    Requires(&'a syn_verus::Expr),
    Invariant(&'a syn_verus::Expr),
    InvariantEnsures(&'a syn_verus::Expr),
    InvariantExceptBreak(&'a syn_verus::Expr),
    Proof(&'a syn_verus::Expr),
}

impl<'a, 'b> GhostVariant<'_> {
    fn expr(&self) -> &syn_verus::Expr {
        match self {
            GhostVariant::Assert(e)
            | GhostVariant::AssertForall(e)
            | GhostVariant::Decreases(e)
            | GhostVariant::Ensures(e)
            | GhostVariant::Recommends(e)
            | GhostVariant::Requires(e)
            | GhostVariant::Invariant(e)
            | GhostVariant::InvariantEnsures(e)
            | GhostVariant::InvariantExceptBreak(e)
            | GhostVariant::Proof(e) => e,
        }
    }

    fn tag(&self) -> &'b str {
        match self {
            GhostVariant::Assert(_) => "assert",
            GhostVariant::AssertForall(_) => "assert_forall",
            GhostVariant::Decreases(_) => "decreases",
            GhostVariant::Ensures(_) => "ensures",
            GhostVariant::Recommends(_) => "recommends",
            GhostVariant::Requires(_) => "requires",
            GhostVariant::Invariant(_) => "invariant",
            GhostVariant::InvariantEnsures(_) => "invariant_ensures",
            GhostVariant::InvariantExceptBreak(_) => "invariant_except_break",
            GhostVariant::Proof(_) => "proof",
        }
    }

    fn detect_non_linear(&self) -> bool {
        detect_non_linear_assert_expr(self.expr())
    }

    /// Return a tuple of the tag and the start and end line of the expression
    /// XXX: We keep this function for backward compatibility of our old code.
    ///      We should return a more detailed location information.
    fn to_tagged_line(&self) -> (&'b str, (usize, usize)) {
        (self.tag(), (self.expr().span().start().line, self.expr().span().end().line))
    }

    /// Return a tuple of the tag and the start line and column of the expression.
    /// The location can be uniquely identify the expression.
    fn to_tagged_start(&self) -> (&'b str, (usize, usize)) {
        (self.tag(), (self.expr().span().start().line, self.expr().span().start().column))
    }

    fn to_tagged_span(&self) -> (&'b str, proc_macro2::Span) {
        (self.tag(), self.expr().span())
    }
}

fn extract_ghost_expr(expr: &syn_verus::Expr) -> Vec<GhostVariant> {
    match expr {
        syn_verus::Expr::Block(bl) => bl.block.stmts.iter().flat_map(extract_ghost_stmt).collect(),
        syn_verus::Expr::If(i) => i
            .then_branch
            .stmts
            .iter()
            .flat_map(extract_ghost_stmt)
            .chain(i.else_branch.as_ref().map_or(vec![], |(_, eexpr)| extract_ghost_expr(&*eexpr)))
            .collect(),
        syn_verus::Expr::Match(m) => m
            .arms
            .iter()
            .flat_map(|arm| {
                arm.guard
                    .as_ref()
                    .map_or(vec![], |(_, gexpr)| extract_ghost_expr(&*gexpr))
                    .into_iter()
                    .chain(extract_ghost_expr(&arm.body))
            })
            .collect(),
        syn_verus::Expr::While(w) => w.invariant.as_ref().map_or(vec![], |i| {
            i.exprs
                .exprs
                .iter()
                .map(GhostVariant::Invariant)
                .chain(w.invariant_ensures.as_ref().map_or(vec![], |ie| {
                    ie.exprs.exprs.iter().map(GhostVariant::InvariantEnsures).collect()
                }))
                .chain(w.invariant_except_break.as_ref().map_or(vec![], |ieb| {
                    ieb.exprs.exprs.iter().map(GhostVariant::InvariantExceptBreak).collect()
                }))
                .chain(w.body.stmts.iter().flat_map(extract_ghost_stmt))
                .collect()
        }),
        syn_verus::Expr::ForLoop(fl) => fl.invariant.as_ref().map_or(vec![], |i| {
            i.exprs
                .exprs
                .iter()
                .map(GhostVariant::Invariant)
                .chain(fl.decreases.as_ref().map_or(vec![], |d| {
                    d.exprs.exprs.iter().map(GhostVariant::Decreases).collect()
                }))
                .chain(fl.body.stmts.iter().flat_map(extract_ghost_stmt))
                .collect()
        }),
        syn_verus::Expr::Loop(l) => l.invariant.as_ref().map_or(vec![], |i| {
            i.exprs
                .exprs
                .iter()
                .map(GhostVariant::Invariant)
                .chain(l.invariant_ensures.as_ref().map_or(vec![], |ie| {
                    ie.exprs.exprs.iter().map(GhostVariant::InvariantEnsures).collect()
                }))
                .chain(l.invariant_except_break.as_ref().map_or(vec![], |ieb| {
                    ieb.exprs.exprs.iter().map(GhostVariant::InvariantExceptBreak).collect()
                }))
                .chain(l.body.stmts.iter().flat_map(extract_ghost_stmt))
                .collect()
        }),
        syn_verus::Expr::TryBlock(t) => t.block.stmts.iter().flat_map(extract_ghost_stmt).collect(),
        syn_verus::Expr::Assert(a) => {
            a.body
                .as_ref()
                .map_or(vec![], |body| {
                    body.stmts.iter().flat_map(extract_ghost_stmt).collect::<Vec<_>>()
                })
                .into_iter()
                .chain(vec![GhostVariant::Assert(expr)])
                .collect()
        }
        syn_verus::Expr::Unary(u) => match u.op {
            syn_verus::UnOp::Proof(_) => extract_ghost_expr(&u.expr)
                .into_iter()
                .chain(vec![GhostVariant::Proof(expr)])
                .collect(),
            _ => vec![],
        },
        syn_verus::Expr::AssertForall(a) => {
            a.body
                .stmts
                .iter()
                .flat_map(extract_ghost_stmt)
                .into_iter()
                .chain(vec![GhostVariant::AssertForall(expr)])
                .collect()
            //vec![GhostVariant::AssertForall(&expr)]
        }
        _ => vec![],
    }
}

fn extract_ghost_stmt(stmt: &syn_verus::Stmt) -> Vec<GhostVariant> {
    match stmt {
        syn_verus::Stmt::Expr(e, _) => extract_ghost_expr(e),
        syn_verus::Stmt::Local(l) => {
            l.init.as_ref().map_or(vec![], |li| extract_ghost_expr(&*li.expr))
        }
        syn_verus::Stmt::Item(i) => extract_ghost_item(i),
        _ => vec![],
    }
}

fn extract_ghost_sig(sig: &syn_verus::Signature) -> Vec<GhostVariant> {
    sig.spec.requires.as_ref().map_or(vec![], |r| {
        r.exprs
            .exprs
            .iter()
            .map(GhostVariant::Requires)
            .chain(sig.spec.ensures.as_ref().map_or(vec![], |e| {
                e.exprs
                    .exprs
                    .iter()
                    .map(GhostVariant::Ensures)
                    .chain(sig.spec.recommends.as_ref().map_or(vec![], |r| {
                        r.exprs.exprs.iter().map(GhostVariant::Recommends).collect()
                    }))
                    .collect()
            }))
            .collect()
    })
}

fn extract_ghost_item(item: &syn_verus::Item) -> Vec<GhostVariant> {
    match item {
        syn_verus::Item::Fn(f) => extract_ghost_sig(&f.sig)
            .into_iter()
            .chain(f.block.stmts.iter().flat_map(extract_ghost_stmt))
            .collect(),
        _ => vec![],
    }
}

pub fn fdetect_nl(filepath: &PathBuf) -> Result<Vec<(&str, (usize, usize))>, Error> {
    fextract_verus_macro(filepath).and_then(|(files, _)| {
        Ok(files
            .iter()
            .flat_map(|file| file.items.iter().flat_map(|item| extract_ghost_item(item)))
            .filter(|gv| gv.detect_non_linear())
            .map(|gv| gv.to_tagged_line())
            .collect())
    })
}

pub fn fget_target(filepath: &PathBuf) -> Result<Vec<FnMethod>, Error> {
    let files = fextract_verus_macro(filepath)?; // Assuming this function is defined elsewhere and returns Result<(Vec<syn_verus::File>, _), Error>
    let mut ret = Vec::new();

    for file in files.0 {
        for item in file.items {
            match item {
                syn_verus::Item::Fn(f) => {
                    if func_is_target(&f) {
                        ret.push(FnMethod::Fn(f.clone()));
                    }
                }
                syn_verus::Item::Impl(i) => {
                    for item in &i.items {
                        if let syn_verus::ImplItem::Fn(m) = item {
                            if method_is_target(&m) {
                                ret.push(FnMethod::Method(
                                    syn_verus::ItemImpl { items: vec![], ..i.clone() },
                                    m.clone(),
                                ));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    Ok(ret)
}

pub fn fget_ghosts(filepath: &PathBuf) -> Result<Vec<(&str, proc_macro2::Span)>, Error> {
    fextract_verus_macro(filepath).and_then(|(files, _)| {
        Ok(files
            .iter()
            .flat_map(|file| file.items.iter().flat_map(|item| extract_ghost_item(item)))
            .map(|gv| gv.to_tagged_span())
            .collect())
    })
}

/// Remove the ghost code of the given `spans` from the function.
/// If the function itself is a ghost function and is included in the `spans`, the function is removed and `None` is returned.
fn remove_invariants_fn(
    fn_item: &syn_verus::ItemFn,
    locs: &Vec<(usize, usize)>,
) -> Option<syn_verus::ItemFn> {
    unimplemented!();
}

fn remove_invariants_impl(
    impl_item: &syn_verus::ItemImpl,
    locs: &Vec<(usize, usize)>,
) -> syn_verus::ItemImpl {
    unimplemented!("remove_invariants_impl")
}

fn remove_invaraints_item(
    item: &syn_verus::Item,
    locs: &Vec<(usize, usize)>,
) -> Option<syn_verus::Item> {
    match item {
        syn_verus::Item::Fn(f) => match remove_invariants_fn(f, locs) {
            Some(f) => Some(syn_verus::Item::Fn(f)),
            None => None,
        },
        syn_verus::Item::Impl(i) => Some(syn_verus::Item::Impl(remove_invariants_impl(i, locs))),
        syn_verus::Item::Trait(t) => unimplemented!("remove_invaraints_item: Trait"),
        _ => Some(item.clone()), // syn_verus::Item::Macro(m) => visit_macro(m),
                                 // syn_verus::Item::Mod(m) => visit_mod(m),
                                 // syn_verus::Item::Use(u) => visit_use(u),
                                 // syn_verus::Item::Struct(s) => visit_struct(s),
                                 // syn_verus::Item::Enum(e) => visit_enum(e),
                                 // syn_verus::Item::Type(t) => visit_type(t),
                                 // syn_verus::Item::Const(c) => visit_const(c),
                                 // syn_verus::Item::Static(s) => visit_static(s),
                                 // syn_verus::Item::Union(u) => visit_union(u),
                                 // syn_verus::Item::TraitAlias(t) => visit_trait_alias(t),
                                 // syn_verus::Item::ExternCrate(e) => visit_extern_crate(e),
                                 // syn_verus::Item::ForeignMod(f) => visit_foreign_mod(f),
                                 // syn_verus::Item::Macro2(m) => visit_macro2(m),
                                 // syn_verus::Item::Verbatim(v) => visit_verbatim(v),
    }
}

fn remove_invaraints_from_file(
    file: &syn_verus::File,
    locs: &Vec<(usize, usize)>,
) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {}

    syn_verus::File { shebang: file.shebang.clone(), attrs: file.attrs.clone(), items: new_items }
}

pub fn fremove_invariants(
    filepath: &PathBuf,
    locs: &Vec<(usize, usize)>,
) -> Result<syn_verus::File, Error> {
    let orig_file = fload_file(filepath)?;
    let pure_file = remove_verus_macro(&orig_file);

    extract_verus_macro(&orig_file).and_then(|verus_macros| {
        let mut verus_files: Vec<syn_verus::File> = Vec::new();

        Ok(deghost_merge_files(&pure_file, verus_files))
    })
}
