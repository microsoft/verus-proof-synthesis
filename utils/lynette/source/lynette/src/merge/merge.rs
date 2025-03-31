use quote::ToTokens;
use syn_verus::punctuated::Punctuated;

use crate::utils::*;
use crate::merge::utils::*;
use crate::DeghostMode;
use crate::merge::is_ghost::IsGhost;
use crate::merge::types::*;
use crate::merge::exprs::*;

fn only_merge_invariants(mode: &DeghostMode) -> bool {
    mode.invariants
        && !mode.requires
        && !mode.ensures
        && !mode.decreases
        && !mode.asserts
        && !mode.assumes
        && !mode.asserts_anno
        && !mode.spec
}

/// Use LCS to merge two vectors of ghost nodes(Item, Stmt or Expr).
/// It is hard to detect semantic conflicts at AST level, so we just merge them.
///
/// Ghost functions(spec and proof) are not recursively merged.
fn merge_ghosts<T: PartialEq + Clone>(items1: &[T], items2: &[T]) -> Vec<T> {
    let lcs = lcs(items1, items2);
    let mut merged = Vec::new();
    let (mut i, mut j) = (0, 0);

    for item in lcs.iter() {
        while i < items1.len() && items1[i] != **item {
            merged.push(items1[i].clone());
            i += 1;
        }

        while j < items2.len() && items2[j] != **item {
            merged.push(items2[j].clone());
            j += 1;
        }

        merged.push((*item).clone());
        i += 1;
        j += 1;
    }

    while i < items1.len() {
        merged.push(items1[i].clone());
        i += 1;
    }

    while j < items2.len() {
        merged.push(items2[j].clone());
        j += 1;
    }

    merged
}

/// `Specifications`` is `Punctuated` expressions, which is a list of expressions separated by punctuations.
/// We assume the order of specifications doesn't matter, so we can sort them before merging to minimize conflicts.
/// The side effect is that we might get "recommend" warnings.
fn merge_specifications(
    spec1: &Specification,
    spec2: &Specification,
) -> Result<Specification, Error> {
    let mut sorted_spec1 =
        spec1.exprs.iter().map(|e| (e.to_token_stream().to_string(), e)).collect::<Vec<(_, _)>>();
    sorted_spec1.sort_by(|a, b| a.0.cmp(&b.0));

    let mut sorted_spec2 =
        spec2.exprs.iter().map(|e| (e.to_token_stream().to_string(), e)).collect::<Vec<(_, _)>>();
    sorted_spec2.sort_by(|a, b| a.0.cmp(&b.0));

    let merged_exprs = merge_ghosts(
        &sorted_spec1.into_iter().map(|(_, e)| e).collect::<Vec<_>>(),
        &sorted_spec2.into_iter().map(|(_, e)| e).collect::<Vec<_>>(),
    );

    let mut punct = Punctuated::new();

    for e in merged_exprs {
        punct.push(e.clone());
        punct.push_punct(syn_verus::token::Comma::default());
    }

    Ok(Specification { exprs: punct })
}

fn merge_options<T: Clone, F>(
    opt1: &Option<T>,
    opt2: &Option<T>,
    merge: F,
) -> Result<Option<T>, Error>
where
    F: FnOnce(&T, &T) -> Result<T, Error>,
{
    match (opt1, opt2) {
        (Some(a), Some(b)) => merge(a, b).map(|c| Some(c)),
        (Some(a), None) => Ok(Some(a.clone())),
        (None, Some(b)) => Ok(Some(b.clone())),
        (None, None) => Ok(None),
    }
}

#[inline]
pub(super) fn merge_invariants(
    inv1: &Option<syn_verus::Invariant>,
    inv2: &Option<syn_verus::Invariant>,
    mode: &DeghostMode,
) -> Result<Option<syn_verus::Invariant>, Error> {
    if mode.invariants {
        merge_options(inv1, inv2, |i1, i2| {
            Ok(syn_verus::Invariant {
                token: syn_verus::token::Invariant::default(),
                exprs: merge_specifications(&i1.exprs, &i2.exprs)?,
            })
        })
    } else {
        Ok(inv1.clone())
    }
}

#[inline]
pub(super) fn merge_requires(
    req1: &Option<syn_verus::Requires>,
    req2: &Option<syn_verus::Requires>,
    mode: &DeghostMode,
) -> Result<Option<syn_verus::Requires>, Error> {
    if mode.requires {
        merge_options(req1, req2, |r1, r2| {
            Ok(syn_verus::Requires {
                token: syn_verus::token::Requires::default(),
                exprs: merge_specifications(&r1.exprs, &r2.exprs)?,
            })
        })
    } else {
        Ok(req1.clone())
    }
}

#[inline]
pub(super) fn merge_ensures(
    ens1: &Option<syn_verus::Ensures>,
    ens2: &Option<syn_verus::Ensures>,
    mode: &DeghostMode,
) -> Result<Option<syn_verus::Ensures>, Error> {
    if mode.ensures {
        merge_options(ens1, ens2, |e1, e2| {
            Ok(syn_verus::Ensures {
                attrs: e1.attrs.clone(),
                token: syn_verus::token::Ensures::default(),
                exprs: merge_specifications(&e1.exprs, &e2.exprs)?,
            })
        })
    } else {
        Ok(ens1.clone())
    }
}

#[inline]
pub(super) fn merge_invariant_ensures(
    inv_ens1: &Option<syn_verus::InvariantEnsures>,
    inv_ens2: &Option<syn_verus::InvariantEnsures>,
    _mode: &DeghostMode,
) -> Result<Option<syn_verus::InvariantEnsures>, Error> {
    merge_options(inv_ens1, inv_ens2, |i1, i2| {
        Ok(syn_verus::InvariantEnsures {
            token: syn_verus::token::InvariantEnsures::default(),
            exprs: merge_specifications(&i1.exprs, &i2.exprs)?,
        })
    }).and_then(|op|
        if op.is_none() {
            Ok(None)
        } else {
            unimplemented!("merge_invariant_ensures")
        }
    )
}

#[inline]
pub(super) fn merge_invariant_except_breaks(
    inv_exc_break1: &Option<syn_verus::InvariantExceptBreak>,
    inv_exc_break2: &Option<syn_verus::InvariantExceptBreak>,
    _mode: &DeghostMode,
) -> Result<Option<syn_verus::InvariantExceptBreak>, Error> {
    merge_options(inv_exc_break1, inv_exc_break2, |i1, i2| {
        Ok(syn_verus::InvariantExceptBreak {
            token: syn_verus::token::InvariantExceptBreak::default(),
            exprs: merge_specifications(&i1.exprs, &i2.exprs)?,
        })
    }).and_then(|op|
        if op.is_none() {
            Ok(None)
        } else {
            unimplemented!("merge_invariant_except_breaks")
        }
    )
}

#[inline]
pub(super) fn merge_decreases(
    dec1: &Option<syn_verus::Decreases>,
    dec2: &Option<syn_verus::Decreases>,
    mode: &DeghostMode,
) -> Result<Option<syn_verus::Decreases>, Error> {
    if mode.decreases {
        merge_options(dec1, dec2, |d1, d2| {
            Ok(syn_verus::Decreases {
                token: syn_verus::token::Decreases::default(),
                exprs: merge_specifications(&d1.exprs, &d2.exprs)?,
            })
        })
    } else {
        Ok(dec1.clone())
    }
}

#[allow(unused)]
#[inline]
fn merge_recommends(
    rec1: &Option<syn_verus::Recommends>,
    rec2: &Option<syn_verus::Recommends>,
    mode: &DeghostMode,
) -> Result<Option<syn_verus::Recommends>, Error> {
    if mode.decreases {
        merge_options(rec1, rec2, |r1, r2| {
            Ok(syn_verus::Recommends {
                token: syn_verus::token::Recommends::default(),
                exprs: merge_specifications(&r1.exprs, &r2.exprs)?,
                via: merge_options(&r1.via, &r2.via, |v1, v2| Ok(v1.clone()))?,
            })
        })
    } else {
        Ok(rec1.clone())
    }
}

fn merge_trait_items(
    item: &TraitItem,
    item1: &TraitItem,
    item2: &TraitItem,
    mode: &DeghostMode,
) -> Result<TraitItem, Error> {
    match (item, item1, item2) {
        (TraitItem::Const(c), TraitItem::Const(c1), TraitItem::Const(c2)) => {
            eq_or_conflict_3(c, c1, c2, "Const conflict", || TraitItem::Const(c.clone()))
        }
        (TraitItem::Fn(m), TraitItem::Fn(m1), TraitItem::Fn(m2)) => {
            match (&m.default, &m1.default, &m2.default) {
                (Some(d), Some(d1), Some(d2)) => {
                    Ok(TraitItem::Fn(syn_verus::TraitItemFn {
                        attrs: m1.attrs.clone(),
                        sig: merge_sigs(&m.sig, &m1.sig, &m2.sig, mode)?,
                        default: Some(merge_blocks(&d.stmts, &d1.stmts, &d2.stmts, mode)?),
                        semi_token: m1.semi_token.clone(),
                    }))
                }
                (None, None, None) => {
                    eq_or_conflict_3(m, m1, m2, "Method conflict", || TraitItem::Fn(m.clone()))
                }
                _ => {
                    return Err(Error::Conflict(String::from("Method default conflict")));
                }
            }
        }
        (TraitItem::Type(t), TraitItem::Type(t1), TraitItem::Type(t2)) => {
            eq_or_conflict_3(t, t1, t2, "Type conflict", || TraitItem::Type(t.clone()))
        }
        (TraitItem::Macro(m), TraitItem::Macro(m1), TraitItem::Macro(m2)) => {
            eq_or_conflict_3(m, m1, m2, "Macro conflict", || TraitItem::Macro(m.clone()))
        }
        (TraitItem::Verbatim(_), TraitItem::Verbatim(_), TraitItem::Verbatim(_)) => {
            unimplemented!("Verbatim trait item");
        }
        _ => Err(Error::Conflict(String::from("Trait item conflict"))),
    }
}

fn merge_item_vec<T: Clone + IsGhost + PartialEq, G>(
    items: &Vec<T>,
    items1: &Vec<T>,
    items2: &Vec<T>,
    merge_fn: G,
    mode: &DeghostMode,
) -> Result<Vec<T>, Error>
where
    G: Fn(&T, &T, &T, &DeghostMode) -> Result<T, Error>,
{
    let mut iter1 = items1.iter().enumerate().peekable();
    let mut iter2 = items2.iter().enumerate().peekable();

    let mut merged_items: Vec<T> = Vec::new();

    for item in items.iter() {
        let st1 = iter_idx_or_err(&mut iter1, "File1 error")?;
        let st2 = iter_idx_or_err(&mut iter2, "File2 error")?;

        // Find all the ghost items until hit the first exec item.
        // `map_or` should not fall into the default case
        while iter1.peek().map_or(false, |(_, i)| i.is_ghost()) {
            iter1.next();
        }

        while iter2.peek().map_or(false, |(_, i)| i.is_ghost()) {
            iter2.next();
        }

        let ed1 = iter_idx_or_err(&mut iter1, "File1 error")?;
        let ed2 = iter_idx_or_err(&mut iter2, "File2 error")?;

        // If we only merge invariants, we do not consider other ghost items. Clone from file1.
        // XXX: we shouldn't be checking this here and only for invariant. We should let the callee decide.
        if only_merge_invariants(mode) {
            merged_items.extend(items1[st1..ed1].iter().cloned());
        } else {
            merged_items.append(&mut merge_ghosts(&items1[st1..ed1], &items2[st2..ed2]));
        }

        // item, iter1.next(), iter2.next() should have the same exec code
        merged_items.push(merge_fn(item, iter1.next().unwrap().1, iter2.next().unwrap().1, mode)?);
    }

    // The remaining items should be ghost items
    let ed1 = items1.len();
    let ed2 = items2.len();

    let st1 = iter_idx_or(&mut iter1, ed1);
    let st2 = iter_idx_or(&mut iter2, ed2);

    if only_merge_invariants(mode) {
        merged_items.extend(items1[st1..ed1].iter().cloned());
    } else {
        merged_items.append(&mut merge_ghosts(&items1[st1..ed1], &items2[st2..ed2]));
    }

    Ok(merged_items)
}

fn merge_traits(
    trait_: &ItemTrait,
    trait1: &ItemTrait,
    trait2: &ItemTrait,
    mode: &DeghostMode,
) -> Result<ItemTrait, Error> {
    let new_items =
        merge_item_vec(&trait_.items, &trait1.items, &trait2.items, merge_trait_items, mode)?;

    Ok(ItemTrait {
        attrs: trait1.attrs.clone(),
        vis: trait1.vis.clone(),
        unsafety: trait1.unsafety.clone(),
        restriction: trait1.restriction.clone(),
        auto_token: trait1.auto_token.clone(),
        trait_token: trait1.trait_token.clone(),
        ident: trait1.ident.clone(),
        generics: trait1.generics.clone(),
        colon_token: trait1.colon_token.clone(),
        supertraits: trait1.supertraits.clone(),
        brace_token: trait1.brace_token.clone(),
        items: new_items,
    })
}



fn merge_stmts(stmt: &Stmt, stmt1: &Stmt, stmt2: &Stmt, mode: &DeghostMode) -> Result<Stmt, Error> {
    match (stmt, stmt1, stmt2) {
        (Stmt::Local(l), Stmt::Local(l1), Stmt::Local(l2)) => {
            eq_or_conflict_3(l, l1, l2, "let-statement conflict", || stmt.clone())
        }
        (Stmt::Item(i), Stmt::Item(i1), Stmt::Item(i2)) => {
            merge_items(i, i1, i2, mode).map(|i| Stmt::Item(i))
        }
        // XXX: Think about the correntness here - current syn_verus removes Stmt::Semi and merge it into Stmt::Expr
        (Stmt::Expr(e, s), Stmt::Expr(e1, _), Stmt::Expr(e2, _)) => {
            // Expr used here cannot be ghost exprs(e.g. assert, assume),
            // but the sub-node can contain ghosts.
            merge_exprs(e, e1, e2, mode).map(|e| Stmt::Expr(e, s.clone()))
        }
        _ => Err(Error::Conflict(String::from("Stmt type conflict"))),
    }
}

pub(super) fn merge_blocks(
    block: &Vec<Stmt>,
    block1: &Vec<Stmt>,
    block2: &Vec<Stmt>,
    mode: &DeghostMode,
) -> Result<syn_verus::Block, Error> {
    let merged_stmts = merge_item_vec(block, block1, block2, merge_stmts, mode)?;

    // We always add the brace_token for safety
    Ok(syn_verus::Block { brace_token: syn_verus::token::Brace::default(), stmts: merged_stmts })
}

fn merge_sigs(
    _sig0: &syn_verus::Signature,
    sig1: &syn_verus::Signature,
    sig2: &syn_verus::Signature,
    mode: &DeghostMode,
) -> Result<syn_verus::Signature, Error> {
    Ok(syn_verus::Signature {
        spec: syn_verus::SignatureSpec {
            requires: merge_requires(&sig1.spec.requires, &sig2.spec.requires, mode)?,
            ensures: merge_ensures(&sig1.spec.ensures, &sig2.spec.ensures, mode)?,
            // recommends: sig1.spec.recommends.clone(), // XXX: We haven't formally support merging recommends
            // decreases: merge_decreases(&sig1.decreases, &sig2.decreases, mode)?,
            ..sig1.spec.clone()
        },
        ..sig1.clone()
    })
}

fn merge_impl_items(
    item: &ImplItem,
    item1: &ImplItem,
    item2: &ImplItem,
    mode: &DeghostMode,
) -> Result<ImplItem, Error> {
    match (item, item1, item2) {
        (ImplItem::Const(c), ImplItem::Const(c1), ImplItem::Const(c2)) => {
            eq_or_conflict_3(c, c1, c2, "Const conflict", || ImplItem::Const(c.clone()))
        }
        (ImplItem::Fn(m), ImplItem::Fn(m1), ImplItem::Fn(m2)) => {
            merge_blocks(&m.block.stmts, &m1.block.stmts, &m2.block.stmts, mode).and_then(|b| {
                Ok(ImplItem::Fn(syn_verus::ImplItemFn {
                    attrs: m1.attrs.clone(),
                    vis: m1.vis.clone(),
                    defaultness: m1.defaultness.clone(),
                    sig: merge_sigs(&m.sig, &m1.sig, &m2.sig, mode)?,
                    block: b,
                    semi_token: m1.semi_token.clone(),
                }))
            })
        }
        (ImplItem::Type(t), ImplItem::Type(t1), ImplItem::Type(t2)) => {
            eq_or_conflict_3(t, t1, t2, "Type conflict", || ImplItem::Type(t.clone()))
        }
        (ImplItem::Macro(m), ImplItem::Macro(m1), ImplItem::Macro(m2)) => {
            eq_or_conflict_3(m, m1, m2, "Macro conflict", || ImplItem::Macro(m.clone()))
        }
        (ImplItem::Verbatim(_), ImplItem::Verbatim(_), ImplItem::Verbatim(_)) => {
            unimplemented!("Verbatim impl item");
        }
        (
            ImplItem::BroadcastGroup(_b),
            ImplItem::BroadcastGroup(_b1),
            ImplItem::BroadcastGroup(_b2),
        ) => {
            // XXX: is this removed for the pure rust function?
            // new_items.push(eq_or_conflict_3(b, b1, b2, "BroadcastGroup conflict", || {
            //     ImplItem::BroadcastGroup(b.clone())
            // })?)
            unimplemented!("BroadcastGroup impl item");
        }
        _ => Err(Error::Conflict(String::from("Impl item conflict"))),
    }
}

fn merge_impls(
    impl_: &syn_verus::ItemImpl,
    impl1: &syn_verus::ItemImpl,
    impl2: &syn_verus::ItemImpl,
    mode: &DeghostMode,
) -> Result<syn_verus::ItemImpl, Error> {
    assert!(impl_.trait_ == impl1.trait_ && impl_.trait_ == impl2.trait_);

    let new_items =
        merge_item_vec(&impl_.items, &impl1.items, &impl2.items, merge_impl_items, mode)?;

    Ok(syn_verus::ItemImpl {
        attrs: impl1.attrs.clone(),
        defaultness: impl1.defaultness.clone(),
        unsafety: impl1.unsafety.clone(),
        impl_token: impl1.impl_token.clone(),
        generics: impl1.generics.clone(),
        trait_: impl1.trait_.clone(),
        self_ty: impl1.self_ty.clone(),
        brace_token: impl1.brace_token.clone(),
        items: new_items,
    })
}

/// fn, fn1, fn2 should have the same exec control flow.
/// fn1 and fn2 can only be exec functions since we've handled ghost functions before.
fn merge_fns(
    fn0: &syn_verus::ItemFn,
    fn1: &syn_verus::ItemFn,
    fn2: &syn_verus::ItemFn,
    mode: &DeghostMode,
) -> Result<syn_verus::ItemFn, Error> {
    Ok(syn_verus::ItemFn {
        attrs: fn1.attrs.clone(),
        vis: fn1.vis.clone(),
        // TODO: ensures and requires are in the signature, we need merge them
        sig: merge_sigs(&fn1.sig, &fn2.sig, &fn2.sig, mode)?,
        block: Box::new(merge_blocks(&fn0.block.stmts, &fn1.block.stmts, &fn2.block.stmts, mode)?),
        semi_token: fn1.semi_token.clone(),
    })
}

fn merge_items(
    item: &syn_verus::Item,
    item1: &syn_verus::Item,
    item2: &syn_verus::Item,
    mode: &DeghostMode,
) -> Result<syn_verus::Item, Error> {
    // item, item1, item2 should be the same type
    use syn_verus::Item;

    match (item, item1, item2) {
        (Item::Const(i), Item::Const(i1), Item::Const(i2)) => {
            eq_or_conflict_3(i, i1, i2, "Const conflict", || item.clone())
        }
        (Item::Enum(e), Item::Enum(e1), Item::Enum(e2)) => {
            eq_or_conflict_3(e, e1, e2, "Enum conflict", || item.clone())
        }
        (Item::ExternCrate(e), Item::ExternCrate(e1), Item::ExternCrate(e2)) => {
            eq_or_conflict_3(e, e1, e2, "ExternCrate conflict", || item.clone())
        }
        (Item::Fn(f), Item::Fn(f1), Item::Fn(f2)) => {
            merge_fns(f, f1, f2, mode).map(|f| Item::Fn(f))
        }
        (Item::ForeignMod(f), Item::ForeignMod(f1), Item::ForeignMod(f2)) => {
            eq_or_conflict_3(f, f1, f2, "ForeignMod conflict", || item.clone())
        }
        (Item::Impl(i), Item::Impl(i1), Item::Impl(i2)) => {
            merge_impls(i, i1, i2, mode).map(|i| Item::Impl(i))
        }
        (Item::Macro(m), Item::Macro(m1), Item::Macro(m2)) => {
            eq_or_conflict_3(m, m1, m2, "Macro conflict", || item.clone())
        }
        (Item::Mod(m), Item::Mod(m1), Item::Mod(m2)) => {
            eq_or_conflict_3(m, m1, m2, "Merging of mod is not supported yet", || item.clone())
        }
        (Item::Static(s), Item::Static(s1), Item::Static(s2)) => {
            eq_or_conflict_3(s, s1, s2, "Static conflict", || item.clone())
        }
        (Item::Struct(s), Item::Struct(s1), Item::Struct(s2)) => {
            eq_or_conflict_3(s, s1, s2, "Struct conflict", || item.clone())
        }
        (Item::Trait(t), Item::Trait(t1), Item::Trait(t2)) => {
            merge_traits(t, t1, t2, mode).map(|t| Item::Trait(t))
        }
        (Item::TraitAlias(t), Item::TraitAlias(t1), Item::TraitAlias(t2)) => {
            eq_or_conflict_3(t, t1, t2, "TraitAlias conflict", || item.clone())
        }
        (Item::Type(t), Item::Type(t1), Item::Type(t2)) => {
            eq_or_conflict_3(t, t1, t2, "Type conflict", || item.clone())
        }
        (Item::Union(u), Item::Union(u1), Item::Union(u2)) => {
            eq_or_conflict_3(u, u1, u2, "Union conflict", || item.clone())
        }
        (Item::Use(u), Item::Use(u1), Item::Use(u2)) => {
            eq_or_conflict_3(u, u1, u2, "Use conflict", || item.clone())
        }
        (Item::Verbatim(_v), Item::Verbatim(_v1), Item::Verbatim(_v2)) => {
            unimplemented!("Verbatim merging is not supported yet");
        }
        _ => Err(Error::Conflict(String::from("Item type conflict"))),
    }
}

pub(super) fn merge_files(
    file: &syn_verus::File,
    file1: &syn_verus::File,
    file2: &syn_verus::File,
    mode: &DeghostMode,
) -> Result<syn_verus::File, Error> {
    let merged_items = merge_item_vec(&file.items, &file1.items, &file2.items, merge_items, mode)?;

    Ok(syn_verus::File {
        shebang: file1.shebang.clone(),
        attrs: file1.attrs.clone(),
        items: merged_items,
    })
}