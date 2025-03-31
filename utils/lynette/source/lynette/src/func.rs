use crate::utils::*;
use quote::ToTokens;
use std::path::PathBuf;

#[allow(dead_code)]
fn replace_function(file: &syn_verus::File, func: &syn_verus::ItemFn) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let syn_verus::Item::Fn(f) = item {
            if f.sig.ident == func.sig.ident {
                new_items.push(syn_verus::Item::Fn(func.clone()));
            } else {
                new_items.push(item.clone());
            }
        } else {
            new_items.push(item.clone());
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

fn remove_function(file: &syn_verus::File, fname: &String) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let syn_verus::Item::Fn(f) = item {
            if f.sig.ident != fname {
                new_items.push(item.clone());
            }
        } else {
            new_items.push(item.clone());
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

pub fn fremove_function(filepath: &PathBuf, function: String) -> Result<syn_verus::File, Error> {
    fextract_verus_macro(filepath).and_then(|(files, orig)| {
        // A list of TokenStreams, one for each macro in the original file
        let tokens: Vec<proc_macro2::TokenStream> = files
            .iter()
            .map(|file| {
                let new_file = remove_function(&file, &function);
                let mut tokens = proc_macro2::TokenStream::new();
                new_file.to_tokens(&mut tokens);
                tokens
            })
            .collect();

        Ok(update_verus_macros_tss(&orig, tokens))
    })
}

pub fn extract_functions_by_name(file: &syn_verus::File, names: &[String]) -> Vec<FnMethod> {
    file.items
        .iter()
        .flat_map(|item| match item {
            syn_verus::Item::Fn(f) => {
                if names.contains(&f.sig.ident.to_string()) {
                    vec![FnMethod::Fn(f.clone())]
                } else {
                    vec![]
                }
            }
            syn_verus::Item::Trait(t) => t
                .items
                .iter()
                .filter_map(|i| {
                    if let syn_verus::TraitItem::Fn(m) = i {
                        if m.default.is_some()
                            && names.contains(&format!(
                                "{}::{}",
                                t.ident.to_string(),
                                m.sig.ident.to_string()
                            ))
                        {
                            Some(FnMethod::MethodDefault(
                                syn_verus::ItemTrait { items: vec![], ..t.clone() },
                                m.clone(),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect::<Vec<FnMethod>>(),
            syn_verus::Item::Impl(ii) => ii
                .items
                .iter()
                .filter_map(|i| {
                    if let syn_verus::ImplItem::Fn(m) = i {
                        if names.contains(dbg!(&format!(
                            "{}::{}",
                            type_path_to_string(&ii.self_ty),
                            m.sig.ident.to_string()
                        ))) {
                            Some(FnMethod::Method(
                                syn_verus::ItemImpl { items: vec![], ..ii.clone() },
                                m.clone(),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect::<Vec<FnMethod>>(),
            _ => vec![],
        })
        .collect::<Vec<FnMethod>>()
}

pub fn fextract_function(filepath: &PathBuf, funcs: &[String]) -> Result<Vec<FnMethod>, Error> {
    fextract_verus_macro(filepath).and_then(|(files, _)| {
        let mut found: Vec<FnMethod> = Vec::new();
        for file in files {
            let res = extract_functions_by_name(&file, funcs);
            found.extend(res);

            if found.len() == funcs.len() {
                break;
            }
        }

        if found.len() < funcs.len() {
            let funcs = funcs
                .iter()
                .filter(|f| !found.iter().any(|fm| fm.get_name() == **f))
                .map(|f| f.to_string())
                .collect::<Vec<String>>()
                .join(", ");
            Err(Error::NotFound(funcs))
        } else {
            Ok(found)
        }
    })
}

pub fn insert_function(
    file: &mut syn_verus::File,
    func: FnMethod,
    replace: bool,
) -> Result<(), Error> {
    match func {
        FnMethod::Fn(f) => {
            let mut found = false;

            for item in file.items.iter_mut() {
                if let syn_verus::Item::Fn(ff) = item {
                    if ff.sig.ident == f.sig.ident {
                        if replace {
                            *item = syn_verus::Item::Fn(f.clone());
                        } else {
                            return Err(Error::Conflict(f.sig.ident.to_string()));
                        }
                        found = true;
                        break;
                    }
                }
            }

            if !found {
                file.items.push(syn_verus::Item::Fn(f));
            }

            Ok(())
        }
        FnMethod::MethodDefault(t, m) => {
            let mut found = false;
            for item in file.items.iter_mut() {
                if let syn_verus::Item::Trait(t) = item {
                    if t.ident != t.ident {
                        continue;
                    }

                    for item in t.items.iter_mut() {
                        if let syn_verus::TraitItem::Fn(mm) = item {
                            if mm.sig.ident == m.sig.ident {
                                if replace {
                                    *item = syn_verus::TraitItem::Fn(m.clone());
                                } else {
                                    return Err(Error::Conflict(m.sig.ident.to_string()));
                                }

                                found = true;
                                break;
                            }
                        }
                    }
                }
            }

            // Adding new trait method is not allowed
            if !found {
                Err(Error::NotFound(t.ident.to_string()))
            } else {
                Ok(())
            }
        }
        FnMethod::Method(i, m) => {
            let mut found = false;

            for item in file.items.iter_mut() {
                if let syn_verus::Item::Impl(ii) = item {
                    if ii.self_ty != i.self_ty || ii.trait_ != i.trait_ {
                        continue;
                    }

                    for item in ii.items.iter_mut() {
                        if let syn_verus::ImplItem::Fn(mm) = item {
                            if mm.sig.ident == m.sig.ident {
                                if replace {
                                    *item = syn_verus::ImplItem::Fn(m.clone());
                                } else {
                                    return Err(Error::Conflict(m.sig.ident.to_string()));
                                }

                                found = true;
                                break;
                            }
                        }
                    }
                }
            }

            if !found {
                // Adding new trait method is not allowed, but adding new struct method is allowed
                if i.trait_.is_none() {
                    file.items.push(syn_verus::Item::Impl(syn_verus::ItemImpl {
                        items: vec![syn_verus::ImplItem::Fn(m)],
                        ..i
                    }));

                    return Ok(());
                }
                return Err(Error::NotFound(i.self_ty.to_token_stream().to_string()));
            } else {
                Ok(())
            }
        }
    }
}

pub fn insert_functions(
    file: &mut syn_verus::File,
    funcs: Vec<FnMethod>,
    replace: bool,
) -> Result<(), Error> {
    for func in funcs {
        insert_function(file, func, replace)?;
    }

    Ok(())
}

pub fn find_all_functions(file: &syn_verus::File) -> Vec<syn_verus::ItemFn> {
    file.items
        .iter()
        .filter_map(|item| if let syn_verus::Item::Fn(f) = item { Some(f.clone()) } else { None })
        .collect::<Vec<syn_verus::ItemFn>>()
}

#[allow(dead_code)]
pub fn ffind_all_functions(filepath: &PathBuf) -> Result<Vec<syn_verus::ItemFn>, Error> {
    fextract_verus_macro(filepath)
        .map(|(files, _)| files.iter().flat_map(|file| find_all_functions(file)).collect())
}

fn detect_non_linear_assert_stmt(stmt: &syn_verus::Stmt) -> bool {
    match stmt {
        syn_verus::Stmt::Local(l) => {
            l.init.as_ref().map_or(false, |l| detect_non_linear_assert_expr(&l.expr))
        }
        syn_verus::Stmt::Item(_) => false,
        syn_verus::Stmt::Expr(e, _) => detect_non_linear_assert_expr(e),
        _ => false,
    }
}

fn expr_only_lit(expr: &syn_verus::Expr) -> bool {
    match expr {
        syn_verus::Expr::Lit(_) => true,
        syn_verus::Expr::Binary(b) => {
            expr_only_lit(b.left.as_ref()) && expr_only_lit(b.right.as_ref())
        }
        syn_verus::Expr::Unary(u) => expr_only_lit(u.expr.as_ref()),
        syn_verus::Expr::Paren(p) => expr_only_lit(p.expr.as_ref()),
        _ => false,
    }
}

pub fn detect_non_linear_assert_expr(expr: &syn_verus::Expr) -> bool {
    match expr {
        syn_verus::Expr::Array(a) => a.elems.iter().any(|e| detect_non_linear_assert_expr(e)),
        syn_verus::Expr::Assign(a) => {
            // XXX: Can lhs be non-linear?
            detect_non_linear_assert_expr(a.right.as_ref())
                || detect_non_linear_assert_expr(&a.left.as_ref())
        }
        syn_verus::Expr::Async(_) => {
            // XXX: Is it allowed in an assert?
            false
        }
        syn_verus::Expr::Await(_) => {
            // XXX: Is it allowed in an assert?
            false
        }
        syn_verus::Expr::Binary(b) => {
            match b.op {
                // XXX: All of the XxxEq ops are removed from syn_verus::BinOp. Need to confirm the effect.
                syn_verus::BinOp::Mul(_) |
                syn_verus::BinOp::Div(_) |
                syn_verus::BinOp::Rem(_) |
                // syn_verus::BinOp::MulEq(_) |
                // syn_verus::BinOp::DivEq(_) |
                // syn_verus::BinOp::RemEq(_) |
                // XXX: Is bit ops non-linear?
                syn_verus::BinOp::BitXor(_) |
                syn_verus::BinOp::BitAnd(_) |
                syn_verus::BinOp::BitOr(_) |
                syn_verus::BinOp::Shl(_) |
                syn_verus::BinOp::Shr(_) |
                // syn_verus::BinOp::BitXorEq(_) |
                // syn_verus::BinOp::BitAndEq(_) |
                // syn_verus::BinOp::BitOrEq(_) |
                // syn_verus::BinOp::ShlEq(_) |
                // syn_verus::BinOp::ShrEq(_) => {
                //     !(expr_only_lit(b.left.as_ref()) || expr_only_lit(b.right.as_ref()))
                // },
                _ => detect_non_linear_assert_expr(b.left.as_ref()) ||
                    detect_non_linear_assert_expr(b.right.as_ref())
            }
        }
        syn_verus::Expr::Block(b) => b.block.stmts.iter().any(|s| detect_non_linear_assert_stmt(s)),
        syn_verus::Expr::Break(_) => false,
        syn_verus::Expr::Call(c) => c.args.iter().any(|e| detect_non_linear_assert_expr(e)),
        syn_verus::Expr::Cast(c) => detect_non_linear_assert_expr(c.expr.as_ref()),
        syn_verus::Expr::Closure(c) => detect_non_linear_assert_expr(c.body.as_ref()),
        syn_verus::Expr::Continue(_) => false,
        syn_verus::Expr::Field(f) => detect_non_linear_assert_expr(&f.base.as_ref()),
        syn_verus::Expr::ForLoop(f) => {
            detect_non_linear_assert_expr(f.expr.as_ref())
                || f.body.stmts.iter().any(|s| detect_non_linear_assert_stmt(s))
        }
        syn_verus::Expr::Group(g) => detect_non_linear_assert_expr(g.expr.as_ref()),
        syn_verus::Expr::If(i) => {
            detect_non_linear_assert_expr(i.cond.as_ref())
                || i.then_branch.stmts.iter().any(|s| detect_non_linear_assert_stmt(s))
                || i.else_branch
                    .as_ref()
                    .map_or(false, |(_, e)| detect_non_linear_assert_expr(e.as_ref()))
        }
        syn_verus::Expr::Index(i) => {
            detect_non_linear_assert_expr(i.index.as_ref())
                || detect_non_linear_assert_expr(i.expr.as_ref())
        }
        syn_verus::Expr::Let(l) => detect_non_linear_assert_expr(l.expr.as_ref()),
        syn_verus::Expr::Lit(_) => false,
        syn_verus::Expr::Loop(l) => l.body.stmts.iter().any(|s| detect_non_linear_assert_stmt(s)),
        syn_verus::Expr::Macro(_) => false,
        syn_verus::Expr::Match(m) => {
            detect_non_linear_assert_expr(m.expr.as_ref())
                || m.arms.iter().any(|a| detect_non_linear_assert_expr(a.body.as_ref()))
        }
        syn_verus::Expr::MethodCall(m) => {
            detect_non_linear_assert_expr(m.receiver.as_ref())
                || m.args.iter().any(|e| detect_non_linear_assert_expr(e))
        }
        syn_verus::Expr::Paren(p) => detect_non_linear_assert_expr(p.expr.as_ref()),
        syn_verus::Expr::Path(_) => false,
        syn_verus::Expr::Range(r) => {
            r.start.as_ref().map_or(false, |e| detect_non_linear_assert_expr(e.as_ref()))
                || r.end.as_ref().map_or(false, |e| detect_non_linear_assert_expr(e.as_ref()))
        }
        syn_verus::Expr::Reference(r) => detect_non_linear_assert_expr(&r.expr.as_ref()),
        syn_verus::Expr::Repeat(r) => {
            detect_non_linear_assert_expr(r.len.as_ref())
                || detect_non_linear_assert_expr(r.expr.as_ref())
        }
        syn_verus::Expr::Return(r) => {
            r.expr.as_ref().map_or(false, |e| detect_non_linear_assert_expr(e))
        }
        syn_verus::Expr::Struct(_) => false,
        syn_verus::Expr::Try(_) => false,
        syn_verus::Expr::TryBlock(_) => false,
        syn_verus::Expr::Tuple(t) => t.elems.iter().any(|e| detect_non_linear_assert_expr(e)),
        syn_verus::Expr::Unary(u) => detect_non_linear_assert_expr(u.expr.as_ref()),
        syn_verus::Expr::Unsafe(_) => false,
        syn_verus::Expr::Verbatim(_) => false,
        syn_verus::Expr::While(w) => {
            detect_non_linear_assert_expr(w.cond.as_ref())
                || w.body.stmts.iter().any(|s| detect_non_linear_assert_stmt(s))
        }
        syn_verus::Expr::Yield(_) => false,
        _ => false,
    }
}

fn detect_non_linear_expr(expr: &syn_verus::Expr) -> bool {
    match expr {
        syn_verus::Expr::Assert(a) => detect_non_linear_assert_expr(a.expr.as_ref()),
        syn_verus::Expr::Block(b) => b.block.stmts.iter().any(|s| detect_non_linear_stmt(s)),
        syn_verus::Expr::ForLoop(f) => {
            //detect_non_linear_assert_expr(f.expr.as_ref()) ||
            f.body.stmts.iter().any(|s| detect_non_linear_stmt(s))
        }
        syn_verus::Expr::If(i) => {
            //detect_non_linear_assert_expr(i.cond.as_ref()) ||
            i.then_branch.stmts.iter().any(|s| detect_non_linear_stmt(s))
                || i.else_branch.as_ref().map_or(false, |(_, e)| detect_non_linear_expr(e.as_ref()))
        }
        syn_verus::Expr::Loop(l) => l.body.stmts.iter().any(|s| detect_non_linear_stmt(s)),
        syn_verus::Expr::Match(m) => {
            //detect_non_linear_assert_expr(m.expr.as_ref()) ||
            m.arms.iter().any(|a| detect_non_linear_expr(a.body.as_ref()))
        }
        syn_verus::Expr::Repeat(r) => {
            //detect_non_linear_assert_expr(r.len.as_ref()) ||
            detect_non_linear_expr(r.expr.as_ref())
        }
        syn_verus::Expr::While(w) => {
            //detect_non_linear_assert_expr(w.cond.as_ref()) ||
            w.body.stmts.iter().any(|s| detect_non_linear_stmt(s))
        }
        _ => false,
    }
}

fn detect_non_linear_stmt(stmt: &syn_verus::Stmt) -> bool {
    match stmt {
        syn_verus::Stmt::Local(_) => false,
        syn_verus::Stmt::Item(_) => false,
        syn_verus::Stmt::Expr(e, _) => detect_non_linear_expr(e), //detect_non_linear_expr(e),
        _ => false,
    }
}

#[allow(dead_code)]
pub fn detect_non_linear_func(func: &syn_verus::ItemFn) -> bool {
    func.block.stmts.iter().any(|s| detect_non_linear_stmt(s))
}
