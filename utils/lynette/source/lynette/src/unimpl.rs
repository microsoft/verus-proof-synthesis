use crate::utils::*;
use once_cell::sync::Lazy;
use quote::ToTokens;
use std::path::PathBuf;
use std::str::FromStr;

type Item = syn_verus::Item;
type Attribute = syn_verus::Attribute;

const EXT_BODY_ATTR_STR: &str = "verifier::external_body";
const EXT_BODY_ATTR_TOKEN: Lazy<proc_macro2::TokenStream> =
    Lazy::new(|| proc_macro2::TokenStream::from_str(EXT_BODY_ATTR_STR).unwrap());
pub const EXT_BODY_ATTR: Lazy<Attribute> = Lazy::new(|| Attribute {
    pound_token: syn_verus::token::Pound::default(),
    style: syn_verus::AttrStyle::Outer,
    bracket_token: syn_verus::token::Bracket::default(),
    //path: syn_verus::parse2::<syn_verus::Path>(EXT_BODY_ATTR_TOKEN.clone()).unwrap(),
    //tokens: proc_macro2::TokenStream::new(),
    // FIXME: this is broken
    meta: syn_verus::Meta::Path(syn_verus::Path {
        leading_colon: None,
        segments: syn_verus::punctuated::Punctuated::new(),
    }),
});

const UNIMPLEMENTED_STR: &str = "unimplemented!()";
const UNIMPLEMENTD_TOEKN: Lazy<proc_macro2::TokenStream> =
    Lazy::new(|| proc_macro2::TokenStream::from_str(UNIMPLEMENTED_STR).unwrap());
const UNIMPLEMENTD_STMT: Lazy<syn_verus::Stmt> = Lazy::new(|| {
    // FIXME: this is broken
    syn_verus::Stmt::Expr(syn_verus::parse2::<syn_verus::Expr>(UNIMPLEMENTD_TOEKN.clone()).unwrap(), None)
});

fn unimpl_block() -> syn_verus::Block {
    syn_verus::Block {
        brace_token: syn_verus::token::Brace::default(),
        stmts: vec![UNIMPLEMENTD_STMT.clone()],
    }
}

fn block_is_unimplemented(b: &syn_verus::Block) -> bool {
    b.stmts.len() == 1
        && (b.stmts[0].to_token_stream().to_string() == "unimplemented ! ()"
            || b.stmts[0].to_token_stream().to_string() == "unimplemented ! ();")
}

fn add_ext_body_attr(attrs: &Vec<Attribute>) -> Vec<Attribute> {
    let mut new_attrs = attrs.clone();

    if !new_attrs.contains(&EXT_BODY_ATTR) {
        new_attrs.push(EXT_BODY_ATTR.clone());
    }

    new_attrs
}

fn unimpl_item(item: &Item, target: bool) -> Item {
    match item {
        Item::Fn(f) => {
            if (!target && func_is_target(f))
                || func_is_ghost(f)
                || func_is_ext_spec(f)
                || block_is_unimplemented(f.block.as_ref())
            {
                item.clone()
            } else {
                Item::Fn(syn_verus::ItemFn {
                    attrs: add_ext_body_attr(&f.attrs),
                    block: Box::new(unimpl_block()),
                    ..f.clone()
                })
            }
        }
        Item::Trait(t) => {
            let new_items = t
                .items
                .iter()
                .map(|i| match i {
                    syn_verus::TraitItem::Fn(m) => {
                        if sig_is_ghost(&m.sig)
                            || (!target && attrs_have_target(&m.attrs))
                            || attrs_have_ext_spec(&m.attrs)
                        {
                            i.clone()
                        } else {
                            if let Some(b) = &m.default {
                                if block_is_unimplemented(b) {
                                    return i.clone();
                                }

                                syn_verus::TraitItem::Fn(syn_verus::TraitItemFn {
                                    attrs: add_ext_body_attr(&m.attrs),
                                    default: Some(unimpl_block()),
                                    ..m.clone()
                                })
                            } else {
                                i.clone()
                            }
                        }
                    }
                    _ => i.clone(),
                })
                .collect::<Vec<_>>();

            Item::Trait(syn_verus::ItemTrait { items: new_items, ..t.clone() })
        }
        Item::Impl(ip) => {
            let new_items = ip
                .items
                .iter()
                .map(|i| match i {
                    syn_verus::ImplItem::Fn(m) => {
                        if method_is_ghost(m)
                            || (!target && method_is_target(m))
                            || method_is_ext_spec(m)
                            || block_is_unimplemented(&m.block)
                        {
                            i.clone()
                        } else {
                            syn_verus::ImplItem::Fn(syn_verus::ImplItemFn {
                                attrs: add_ext_body_attr(&m.attrs),
                                block: unimpl_block(),
                                ..m.clone()
                            })
                        }
                    }
                    _ => i.clone(),
                })
                .collect::<Vec<_>>();

            Item::Impl(syn_verus::ItemImpl { items: new_items, ..ip.clone() })
        }
        _ => item.clone(),
    }
}

fn unimpl_one<T, F, G, H>(
    orig_items: &[T],
    unimpl_items: &[T],
    unimpl_files: &Vec<syn_verus::File>,
    i: usize,
    j: usize,
    item_constructor: F,
    item_matcher: G,
    item_ident: H,
) -> Vec<(String, Vec<syn_verus::File>)>
where
    T: Clone + PartialEq,
    F: Fn(Vec<T>) -> syn_verus::Item,
    G: Fn(&T) -> bool,
    H: Fn(&T) -> String,
{
    let mut unimpl_each: Vec<(String, Vec<syn_verus::File>)> = Vec::new();

    for k in 0..unimpl_items.len() {
        let orig_i = &orig_items[k];
        let unimpl_i = &unimpl_items[k];

        if orig_i == unimpl_i {
            continue;
        }

        if item_matcher(orig_i) {
            let mut unimpl_one_files = unimpl_files.clone();

            unimpl_one_files[i].items[j] = item_constructor(
                unimpl_items
                    .iter()
                    .enumerate()
                    .map(|(l, item)| if l == k { orig_i.clone() } else { item.clone() })
                    .collect(),
            );

            unimpl_each.push((item_ident(unimpl_i), unimpl_one_files));
        }
    }

    unimpl_each
}

pub fn funimpl_file(
    filepath: &PathBuf,
    target: bool,
) -> Result<Vec<(String, syn_verus::File)>, Error> {
    fextract_verus_macro(filepath).map(|(files, orig)| {
        let new_files = files
            .iter()
            .map(|file| syn_verus::File {
                shebang: file.shebang.clone(),
                attrs: file.attrs.clone(),
                items: file
                    .items
                    .iter()
                    .map(|item| unimpl_item(item, target))
                    .collect::<Vec<syn_verus::Item>>(),
            })
            .collect::<Vec<syn_verus::File>>();

        let mut unimpl_each: Vec<(String, Vec<syn_verus::File>)> = Vec::new();

        for i in 0..new_files.len() {
            let orig_file = &files[i];
            let unimpl_file = &new_files[i];

            for j in 0..unimpl_file.items.len() {
                let orig_item = &orig_file.items[j];
                let unimpl_item = &unimpl_file.items[j];

                if orig_item == unimpl_item {
                    continue;
                }

                match (orig_item, unimpl_item) {
                    (Item::Fn(f), Item::Fn(_)) => {
                        let mut unimpl_files = new_files.clone();

                        unimpl_files[i].items[j] = orig_item.clone();

                        unimpl_each.push((f.sig.ident.to_string(), unimpl_files));
                    }
                    (Item::Trait(orig_t), Item::Trait(unimpl_t)) => unimpl_each.extend(unimpl_one(
                        &orig_t.items,
                        &unimpl_t.items,
                        &new_files,
                        i,
                        j,
                        |items| Item::Trait(syn_verus::ItemTrait { items, ..unimpl_t.clone() }),
                        |i| match i {
                            syn_verus::TraitItem::Fn(m) => {
                                !(sig_is_ghost(&m.sig)
                                    || (!target && attrs_have_target(&m.attrs))
                                    || attrs_have_ext_spec(&m.attrs))
                            }
                            _ => false,
                        },
                        |i| match i {
                            syn_verus::TraitItem::Fn(m) => {
                                format!("{}::{}", orig_t.ident.to_string(), m.sig.ident.to_string())
                            }
                            _ => String::new(),
                        },
                    )),
                    (Item::Impl(orig_i), Item::Impl(unimpl_i)) => unimpl_each.extend(unimpl_one(
                        &orig_i.items,
                        &unimpl_i.items,
                        &new_files,
                        i,
                        j,
                        |items| Item::Impl(syn_verus::ItemImpl { items, ..unimpl_i.clone() }),
                        |i| match i {
                            syn_verus::ImplItem::Fn(m) => {
                                !(method_is_ghost(m)
                                    || (!target && method_is_target(m))
                                    || method_is_ext_spec(m))
                            }
                            _ => false,
                        },
                        |i| match i {
                            // XXX:
                            // A struct may have mulitple implementations of methods
                            // with the same name but in different traits.
                            // Unfortunatly, verus does not distinguish between these
                            // methods.
                            // When --verify-function specify a method name with ambiguity,
                            // verus verifies both.
                            // Thus we just keep the same behavior here for now.
                            syn_verus::ImplItem::Fn(m) => {
                                format!(
                                    "{}::{}",
                                    type_path_to_string(&orig_i.self_ty),
                                    m.sig.ident.to_string()
                                )
                            }
                            _ => String::new(),
                        },
                    )),
                    _ => {
                        continue;
                    }
                }
            }
        }

        unimpl_each
            .into_iter()
            .map(|(name, fs)| (name, update_verus_macros_files(&orig, fs)))
            .collect()
    })
}
