use syn_verus::visit_mut::{VisitMut};
use syn_verus::parse_quote;
use quote::ToTokens;
use super::benchmark_utils::*;

/*
Remove all uses besides use vstd::prelude::*;
*/

fn should_remove(u: &syn_verus::UseTree) -> bool {
    let vstd_prelude: syn_verus::UseTree = parse_quote! {
        vstd::prelude::*
    };
    // TODO: temporary hack
    let vstd_slice : syn_verus::UseTree = parse_quote! {
        vstd::slice::*
    };
    let vstd_bytes : syn_verus::UseTree = parse_quote! {
        vstd::bytes::*
    };
    let s = u.to_token_stream().to_string();
    s.contains("vstd") && *u != vstd_prelude && *u != vstd_slice && *u != vstd_bytes
}

struct CleanUsesVisitor;

impl VisitMut for CleanUsesVisitor {
    fn visit_file_mut(&mut self, i: &mut syn_verus::File) {
        let mut new_items = Vec::new();
        for idx in 0..i.items.len() {
            let item = i.items[idx].clone();
            match item {
                syn_verus::Item::Use(ref u) => {
                    if !should_remove(&u.tree) {
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

pub fn clean_uses(file: &mut syn_verus::File) {
    let mut clean_uses_visitor = CleanUsesVisitor {};
    clean_uses_visitor.visit_file_mut(file);

    // clean inside verus macro
    let mut macro_visitor = VerusMacroVisitor { visitor: clean_uses_visitor };
    macro_visitor.visit_file_mut(file);
}
