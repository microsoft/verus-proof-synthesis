use crate::{utils::*, DeghostMode};
use proc_macro2::TokenStream;
use quote::ToTokens;
use std::path::PathBuf;
use syn_verus::Token;
use syn_verus::TraitItemMethod;

fn remove_ghost_local(local: &syn_verus::Local) -> Option<syn_verus::Local> {
    match local.ghost {
        Some(_) => None,
        None => Some(local.clone()),
    }
}

fn remove_ghost_expr(expr: &syn_verus::Expr, mode: &DeghostMode) -> Option<syn_verus::Expr> {
    //println!("{}\n", expr.to_token_stream().to_string());
    match expr {
        syn_verus::Expr::Block(b) => remove_ghost_block(&b.block, mode).map(|new_block| {
            syn_verus::Expr::Block(syn_verus::ExprBlock {
                attrs: b.attrs.clone(),
                label: b.label.clone(),
                block: syn_verus::Block {
                    brace_token: b.block.brace_token.clone(),
                    stmts: new_block.stmts,
                },
            })
        }),
        syn_verus::Expr::Call(c) => {
            let new_args: syn_verus::punctuated::Punctuated<syn_verus::Expr, Token![,]> = c
                .args
                .iter()
                .map(|arg| {
                    if let syn_verus::Expr::Closure(c) = arg {
                        remove_ghost_expr(&*c.body, mode).unwrap()
                    } else {
                        arg.clone()
                    }
                })
                .collect();

            Some(syn_verus::Expr::Call(syn_verus::ExprCall {
                attrs: c.attrs.clone(),
                func: c.func.clone(),
                paren_token: c.paren_token.clone(),
                args: new_args,
            }))
        }
        syn_verus::Expr::Closure(c) => remove_ghost_expr(&*c.body, mode).map(|new_body| {
            syn_verus::Expr::Closure(syn_verus::ExprClosure {
                attrs: c.attrs.clone(),
                asyncness: c.asyncness.clone(),
                movability: c.movability.clone(),
                capture: c.capture.clone(),
                or1_token: c.or1_token.clone(),
                inputs: c.inputs.clone(),
                or2_token: c.or2_token.clone(),
                output: c.output.clone(),
                requires: if mode.requires { c.requires.clone() } else { None },
                ensures: if mode.ensures { c.ensures.clone() } else { None },
                inner_attrs: c.inner_attrs.clone(),
                body: Box::new(new_body),
            })
        }),
        syn_verus::Expr::While(w) => {
            /*
             * Fields to remove:
             * - invariant_except_break
             * - invariant
             * - invariant_ensures
             * - ensures
             * - decreases
             */
            remove_ghost_block(&w.body, mode).map(|new_body| {
                syn_verus::Expr::While(syn_verus::ExprWhile {
                    attrs: w.attrs.clone(),
                    label: w.label.clone(),
                    while_token: w.while_token.clone(),
                    cond: w.cond.clone(),
                    body: new_body,
                    invariant_except_break: None, // Removed
                    invariant: None,              // Removed
                    invariant_ensures: None,      // Removed
                    ensures: None,                // Removed
                    decreases: None,              // Removed
                })
            })
        }
        syn_verus::Expr::ForLoop(f) => {
            /*
             * Fields to remove:
             * - invariant
             * - decreases
             */
            remove_ghost_block(&f.body, mode).map(|new_body| {
                syn_verus::Expr::ForLoop(syn_verus::ExprForLoop {
                    attrs: f.attrs.clone(),
                    label: f.label.clone(),
                    for_token: f.for_token.clone(),
                    pat: f.pat.clone(),
                    in_token: f.in_token.clone(),
                    expr: f.expr.clone(),
                    body: new_body,
                    expr_name: f.expr_name.clone(),
                    invariant: None, // Removed
                    decreases: None, // Removed
                })
            })
        }
        syn_verus::Expr::Unary(u) => {
            match u.op {
                /*
                 * verus:
                 * Proof
                 * Forall
                 * Exists
                 * Choose
                 */
                syn_verus::UnOp::Proof(_)
                | syn_verus::UnOp::Forall(_)
                | syn_verus::UnOp::Exists(_)
                | syn_verus::UnOp::Choose(_) => None,
                _ => Some(expr.clone()),
            }
        }
        syn_verus::Expr::If(i) => {
            remove_ghost_block(&i.then_branch, mode).and_then(|new_then_branch| {
                if let Some((else_token, else_expr)) = i.else_branch.as_ref() {
                    remove_ghost_expr(&*else_expr, mode).map(|new_else_branch| {
                        syn_verus::Expr::If(syn_verus::ExprIf {
                            attrs: i.attrs.clone(),
                            if_token: i.if_token.clone(),
                            cond: i.cond.clone(),
                            then_branch: new_then_branch,
                            else_branch: Some((else_token.clone(), Box::new(new_else_branch))),
                        })
                    })
                } else {
                    Some(syn_verus::Expr::If(syn_verus::ExprIf {
                        attrs: i.attrs.clone(),
                        if_token: i.if_token.clone(),
                        cond: i.cond.clone(),
                        then_branch: new_then_branch,
                        else_branch: None,
                    }))
                }
            })
        }
        syn_verus::Expr::Match(m) => {
            let new_arms: Vec<syn_verus::Arm> = m
                .arms
                .iter()
                .filter_map(|arm| {
                    remove_ghost_expr(&*arm.body, mode).map(|new_body| syn_verus::Arm {
                        attrs: arm.attrs.clone(),
                        pat: arm.pat.clone(),
                        guard: arm.guard.clone(),
                        fat_arrow_token: arm.fat_arrow_token.clone(),
                        body: Box::new(new_body),
                        comma: arm.comma.clone(),
                    })
                })
                .collect();

            Some(syn_verus::Expr::Match(syn_verus::ExprMatch {
                attrs: m.attrs.clone(),
                match_token: m.match_token.clone(),
                expr: m.expr.clone(),
                brace_token: m.brace_token.clone(),
                arms: new_arms,
            }))
        }
        // veurs:
        syn_verus::Expr::Assert(a) => {
            fn annotated_assert(a: &syn_verus::Assert) -> bool {
                a.attrs.iter().any(|attr| attr.tokens.to_string() == "(llm_do_not_change)")
            }

            if mode.asserts || (mode.asserts_anno && annotated_assert(a)) {
                Some(expr.clone())
            } else {
                None
            }
        }
        syn_verus::Expr::Assume(..)
        | syn_verus::Expr::AssertForall(..)
        | syn_verus::Expr::RevealHide(..)
        | syn_verus::Expr::View(..)
        | syn_verus::Expr::BigAnd(..)
        | syn_verus::Expr::BigOr(..)
        | syn_verus::Expr::Is(..)
        | syn_verus::Expr::Has(..)
        | syn_verus::Expr::Matches(..)
        | syn_verus::Expr::GetField(..) => None,
        _ => Some(expr.clone()),
    }
}

fn remove_ghost_stmt(stmt: &syn_verus::Stmt, mode: &DeghostMode) -> Option<syn_verus::Stmt> {
    match stmt {
        syn_verus::Stmt::Local(l) => remove_ghost_local(l).map(syn_verus::Stmt::Local),
        syn_verus::Stmt::Item(i) => {
            // While we do have visit_item, I am not sure if we need to visit the item here
            // or just keep it as is.
            Some(syn_verus::Stmt::Item(i.clone()))
            // match visit_item(i) {
            //     Some(new_item) => Some(syn_verus::Stmt::Item(new_item)),
            //     None => None
            // }
        }
        syn_verus::Stmt::Expr(e) => remove_ghost_expr(e, mode).map(syn_verus::Stmt::Expr),
        syn_verus::Stmt::Semi(e, _semi) => remove_ghost_expr(e, mode)
            .map(|new_expr| syn_verus::Stmt::Semi(new_expr, _semi.clone())),
    }
}

fn remove_ghost_block(block: &syn_verus::Block, mode: &DeghostMode) -> Option<syn_verus::Block> {
    let new_stms: Vec<syn_verus::Stmt> =
        block.stmts.iter().filter_map(|stmt| remove_ghost_stmt(stmt, mode)).collect();

    if new_stms.is_empty() {
        return None;
    }

    Some(syn_verus::Block { brace_token: block.brace_token.clone(), stmts: new_stms })
}

fn remove_ghost_sig(
    sig: &syn_verus::Signature,
    mode: &DeghostMode,
) -> Option<syn_verus::Signature> {
    /*
     * Fields to remove:
     * - publish
     * - broadcast
     * - prover
     * - mode
     * - requires
     * - ensures
     * - recommends
     * - decreases
     * - invariants
     */
    if (!mode.spec
        && matches!(sig.mode, syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)))
        || matches!(sig.mode, syn_verus::FnMode::Proof(_))
    {
        return None;
    }

    Some(syn_verus::Signature {
        publish: syn_verus::Publish::Default, // Removed
        constness: sig.constness.clone(),
        asyncness: sig.asyncness.clone(),
        unsafety: sig.unsafety.clone(),
        abi: sig.abi.clone(),
        broadcast: sig.broadcast.clone(), // Removed
        mode: sig.mode.clone(),           // Removed
        fn_token: sig.fn_token.clone(),
        ident: sig.ident.clone(),
        generics: sig.generics.clone(),
        paren_token: sig.paren_token.clone(),
        inputs: sig.inputs.clone(),
        variadic: sig.variadic.clone(),
        output: match mode.sig_output {
            true => sig.output.clone(),
            false => match &sig.output {
                syn_verus::ReturnType::Type(_, _, _, ty) => {
                    syn_verus::ReturnType::Type(Default::default(), None, None, ty.clone())
                }
                syn_verus::ReturnType::Default => syn_verus::ReturnType::Default,
            }
        },
        prover: sig.prover.clone(), // Removed
        // TODO: This fix needs to be propagated to other places using `Specification`
        requires: sig
            .requires
            .clone()
            .map(|mut new_req| {
                if !new_req.exprs.exprs.trailing_punct() {
                    new_req.exprs.exprs.push_punct(Default::default());
                }
                new_req
            })
            .filter(|_| mode.requires), // Removed
        recommends: sig.recommends.clone().map(|mut new_rec| {
            if !new_rec.exprs.exprs.trailing_punct() {
                new_rec.exprs.exprs.push_punct(Default::default());
            }
            new_rec
        }), // Removed
        ensures: sig
            .ensures
            .clone()
            .map(|mut new_ens| {
                if !new_ens.exprs.exprs.trailing_punct() {
                    new_ens.exprs.exprs.push_punct(Default::default());
                }
                new_ens
            })
            .filter(|_| mode.ensures), // Removed
        decreases: sig
            .decreases
            .clone()
            .map(|mut new_dec| {
                if !new_dec.decreases.exprs.exprs.trailing_punct() {
                    new_dec.decreases.exprs.exprs.push_punct(Default::default());
                }
                new_dec
            })
            .filter(|_| mode.decreases), // Removed
        invariants: sig.invariants.clone().filter(|_| mode.invariants), // Removed
    })
}

fn is_verifier_attr(attr: &syn_verus::Attribute) -> bool {
    attr.path.segments.len() > 0 && attr.path.segments[0].ident.to_string() == "verifier"
}

fn remove_verifier_attr(attr: &Vec<syn_verus::Attribute>) -> Vec<syn_verus::Attribute> {
    attr.iter().filter(|a| !is_verifier_attr(a)).map(|a| a.clone()).collect()
}

/*
 * Target Mode:
 *  Executable function: qualifiers cannot be modifified; executable part cannot be modified
 *  spec function: cannot be modified at all
 *  proof function: do not care at all
 * Non-Target Mode:
 *  Executable function: qualifiers can be modified; executable part cannot be modified
 *  spec function: do not care at all
 *  proof function: do not care at all
 */

fn remove_ghost_fn(func: &syn_verus::ItemFn, mode: &DeghostMode) -> Option<syn_verus::ItemFn> {
    remove_ghost_sig(&func.sig, mode).and_then(|new_sig| {
        if matches!(new_sig.mode, syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)) {
            Some(func.clone())
        } else {
            remove_ghost_block(&(*func.block), mode).map(|new_block| {
                syn_verus::ItemFn {
                    attrs: remove_verifier_attr(&func.attrs),
                    vis: func.vis.clone(),
                    sig: new_sig,
                    block: Box::new(new_block), // Box the new block
                    semi_token: func.semi_token.clone(), // XXX: What is this?
                }
            })
        }
    })
}

fn remove_ghost_impl(i: &syn_verus::ItemImpl, mode: &DeghostMode) -> syn_verus::ItemImpl {
    syn_verus::ItemImpl {
        attrs: i.attrs.clone(),
        defaultness: i.defaultness.clone(),
        unsafety: i.unsafety.clone(),
        impl_token: i.impl_token.clone(),
        generics: i.generics.clone(),
        trait_: i.trait_.clone(),
        self_ty: i.self_ty.clone(),
        brace_token: i.brace_token.clone(),
        items: i
            .items
            .iter()
            .filter_map(|it| {
                if let syn_verus::ImplItem::Method(func) = it {
                    remove_ghost_sig(&func.sig, mode).and_then(|new_sig| {
                        {
                            if matches!(
                                new_sig.mode,
                                syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)
                            ) {
                                Some(func.clone())
                            } else {
                                remove_ghost_block(&func.block, mode).map(|new_block| {
                                    syn_verus::ImplItemMethod {
                                        attrs: func.attrs.clone(),
                                        vis: func.vis.clone(),
                                        defaultness: func.defaultness.clone(),
                                        sig: new_sig,
                                        block: new_block,
                                        semi_token: func.semi_token.clone(), // XXX: What is this?
                                    }
                                })
                            }
                        }
                        .and_then(|new_method| Some(syn_verus::ImplItem::Method(new_method)))
                    })
                } else {
                    Some(it.clone())
                }
            })
            .collect(),
    }
}

fn remove_ghost_item(item: &syn_verus::Item, mode: &DeghostMode) -> Option<syn_verus::Item> {
    match item {
        syn_verus::Item::Fn(f) => match remove_ghost_fn(f, mode) {
            Some(new_func) => Some(syn_verus::Item::Fn(new_func)),
            None => None,
        },
        syn_verus::Item::Impl(i) => Some(syn_verus::Item::Impl(remove_ghost_impl(i, mode))),
        syn_verus::Item::Trait(t) => Some(syn_verus::Item::Trait(syn_verus::ItemTrait {
            attrs: t.attrs.clone(),
            vis: t.vis.clone(),
            unsafety: t.unsafety.clone(),
            auto_token: t.auto_token.clone(),
            trait_token: t.trait_token.clone(),
            ident: t.ident.clone(),
            generics: t.generics.clone(),
            colon_token: t.colon_token.clone(),
            supertraits: t.supertraits.clone(),
            brace_token: t.brace_token.clone(),
            items: t
                .items
                .iter()
                .filter_map(|i| match i {
                    syn_verus::TraitItem::Method(func) => {
                        Some(syn_verus::TraitItem::Method(TraitItemMethod {
                            attrs: func.attrs.clone(),
                            sig: remove_ghost_sig(&func.sig, mode)?,
                            default: func.default.as_ref().map(|b| {
                                remove_ghost_block(b, mode).unwrap_or_else(|| syn_verus::Block {
                                    brace_token: Default::default(),
                                    stmts: Vec::new(),
                                })
                            }),
                            semi_token: func.semi_token.clone(),
                        }))
                    }
                    _ => Some(i.clone()),
                })
                .collect::<Vec<syn_verus::TraitItem>>(),
        })),
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

pub fn remove_ghost_from_file(file: &syn_verus::File, mode: &DeghostMode) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let Some(item) = remove_ghost_item(item, mode) {
            new_items.push(item);
        }
    }

    let new_file = syn_verus::File {
        shebang: file.shebang.clone(),
        attrs: file.attrs.clone(),
        items: new_items,
    };

    new_file
}

fn remove_verus_macro(file: &syn_verus::File) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        if let syn_verus::Item::Macro(m) = item {
            if !is_verus_macro(&m.mac) {
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

fn merge_files(file: &syn_verus::File, verus_files: Vec<syn_verus::File>) -> syn_verus::File {
    let mut new_items: Vec<syn_verus::Item> = Vec::new();

    for item in &file.items {
        new_items.push(item.clone());
    }

    for verus_file in verus_files {
        for item in &verus_file.items {
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

pub fn fextract_pure_rust(filepath: PathBuf, mode: &DeghostMode) -> Result<syn_verus::File, Error> {
    let orig_file = fload_file(&filepath)?;
    let pure_file = remove_verus_macro(&orig_file);

    extract_verus_macro(&orig_file).and_then(|verus_macros| {
        let mut verus_files: Vec<syn_verus::File> = Vec::new();
        for vm in verus_macros {
            let new_verus_file = remove_ghost_from_file(&vm, mode);

            let mut new_verus_ts = TokenStream::new();

            new_verus_file.to_tokens(&mut new_verus_ts);
            verus_files.push(new_verus_file);
        }

        //println!("{}", fprint_file(&merge_files(&pure_file, verus_files.clone()), VFormatter::VerusFmt));

        Ok(merge_files(&pure_file, verus_files))
    })
}
