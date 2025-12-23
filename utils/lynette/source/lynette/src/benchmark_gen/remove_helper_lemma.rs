use syn_verus::visit_mut::{VisitMut};
use crate::{DeghostMode};
use crate::deghost::{remove_ghost_block};
use super::benchmark_utils::*;

/*
Remove any standalone helper lemmas and lemmas implemented for structs.
Do not remove axioms or lemmas within traits (those are treated like axioms).
*/

fn is_proof(mode: &syn_verus::FnMode) -> bool {
    match mode {
        syn_verus::FnMode::Proof(_) => true,
        _ => false
    }
}

struct RemoveHelperLemmaVisitor;

impl VisitMut for RemoveHelperLemmaVisitor {
    fn visit_file_mut(&mut self, i: &mut syn_verus::File) {
        let mut new_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match item {
                syn_verus::Item::Fn(ref f) => {
                    if top_level_fn_is_target(&f) || !is_proof(&f.sig.mode) {
                        new_items.push(item);
                    }
                },
                syn_verus::Item::Impl(mut imp) => {
                    self.visit_item_impl_mut(&mut imp);
                    new_items.push(syn_verus::Item::Impl(imp));
                },
                _ => {
                    new_items.push(item);
                }
            }
        }
        i.items = new_items;
    }

    fn visit_item_impl_mut(&mut self, i: &mut syn_verus::ItemImpl) {
        let mut new_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match i.items[idx] {
                syn_verus::ImplItem::Fn(ref f) => {
                    if impl_fn_is_target(&f) || !is_proof(&f.sig.mode) {
                        new_items.push(item);
                    }
                },
                _ => {
                    new_items.push(item);
                }
            }
        }
        i.items = new_items;
    }
}

pub fn remove_helper_lemma(file: &mut syn_verus::File) {
    let lemma_visitor = RemoveHelperLemmaVisitor {};
    let mut macro_visitor = VerusMacroVisitor { visitor: lemma_visitor };
    macro_visitor.visit_file_mut(file);
}
