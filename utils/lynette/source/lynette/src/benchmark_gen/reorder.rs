use std::path::PathBuf;
use syn_verus::visit_mut::{VisitMut};
use quote::ToTokens;
use crate::{utils::is_verus_macro, Error};
use super::benchmark_utils::*;

struct ReorderTargetFnVisitor {
    found_target: bool
}

impl VisitMut for ReorderTargetFnVisitor {
    fn visit_file_mut(&mut self, i: &mut syn_verus::File) {
        let mut new_items = Vec::new();
        let mut target_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match item {
                syn_verus::Item::Fn(ref f) => {
                    if top_level_fn_is_target(&f) {
                        self.found_target = true;
                        target_items.push(item);
                    } else {
                        new_items.push(item);
                    }
                },
                syn_verus::Item::Impl(mut imp) => {
                    let found_before = self.found_target;
                    self.visit_item_impl_mut(&mut imp);
                    let new_item = syn_verus::Item::Impl(imp);
                    if !found_before && self.found_target {
                        target_items.push(new_item);
                    } else {
                        new_items.push(new_item);
                    }
                },
                syn_verus::Item::Trait(mut t) => {
                    let found_before = self.found_target;
                    self.visit_item_trait_mut(&mut t);
                    let new_item = syn_verus::Item::Trait(t);
                    if !found_before && self.found_target {
                        target_items.push(new_item);
                    } else {
                        new_items.push(new_item);
                    }
                },
                _ => {
                    new_items.push(item);
                }
            }
        }
        new_items.extend(target_items);
        i.items = new_items;
    }

    fn visit_item_impl_mut(&mut self, i: &mut syn_verus::ItemImpl) {
        let mut new_items = Vec::new();
        let mut target_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match i.items[idx] {
                syn_verus::ImplItem::Fn(ref f) => {
                    if impl_fn_is_target(&f) {
                        self.found_target = true;
                        target_items.push(item);
                    } else {
                        new_items.push(item);
                    }
                },
                _ => {
                    new_items.push(item);
                }
            }
        }
        new_items.extend(target_items);
        i.items = new_items;
    }

    fn visit_item_trait_mut(&mut self, i: &mut syn_verus::ItemTrait) {
        let mut new_items = Vec::new();
        let mut target_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match i.items[idx] {
                syn_verus::TraitItem::Fn(ref f) => {
                    if trait_fn_is_target(&f) {
                        self.found_target = true;
                        target_items.push(item);
                    } else {
                        new_items.push(item);
                    }
                },
                _ => {
                    new_items.push(item);
                }
            }
        }
        new_items.extend(target_items);
        i.items = new_items;
    }
}

pub fn order_target_item_last(file: &mut syn_verus::File) {
    let reorder_visitor = ReorderTargetFnVisitor { found_target: false };
    let mut macro_visitor = VerusMacroVisitor { visitor: reorder_visitor };
    macro_visitor.visit_file_mut(file);
}
