use syn_verus::visit_mut::{VisitMut};
use syn_verus::parse_quote;
use crate::{DeghostMode};
use crate::deghost::{remove_ghost_block};
use crate::additions::{remove_proof_attr};
use super::benchmark_utils::*;

/*
Ghost to erase on target fn:
- within proof body
- within signatures
- proof-related attributes

Ghost to erase on other fns:
- proof-related attributes
*/

fn empty_block(b: &mut syn_verus::Block) {
    b.stmts = Vec::new();
}

fn has_return(sig: &syn_verus::Signature) -> bool {
    match &sig.output {
        syn_verus::ReturnType::Default => false,
        syn_verus::ReturnType::Type(..) => true
    }
}

fn default_return_block(b: &mut syn_verus::Block) {
    b.stmts = Vec::new();
    let proof_from_false = parse_quote! {
        proof_from_false()
    };
    b.stmts.push(syn_verus::Stmt::Expr(proof_from_false, None));
}

fn erase_ghost_sig(sig: &mut syn_verus::SignatureSpec) {
    sig.prover = None;
    sig.decreases = None;
    sig.invariants = None;
}

struct EraseGhostVisitor;

impl VisitMut for EraseGhostVisitor {
    fn visit_impl_item_fn_mut(&mut self, i: &mut syn_verus::ImplItemFn) {
        if impl_fn_is_target(&i) {
            match i.sig.mode {
                syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default => {
                    match remove_ghost_block(&i.block, &DeghostMode::default()) {
                        Some(b) => {
                            i.block = b;
                        },
                        None => {
                            empty_block(&mut i.block);
                        }
                    }
                },
                syn_verus::FnMode::Proof(_) => {
                    if has_return(&i.sig) {
                        default_return_block(&mut i.block);
                    } else {
                        empty_block(&mut i.block);
                    }
                }
                _ => {}
            }
            i.attrs = remove_proof_attr(&i.attrs);
            erase_ghost_sig(&mut i.sig.spec);
        } else {
            i.attrs = remove_proof_attr(&i.attrs);
        }
    }

    fn visit_item_fn_mut(&mut self, i: &mut syn_verus::ItemFn) {
        if top_level_fn_is_target(&i) {
            match i.sig.mode {
                syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default => {
                    match remove_ghost_block(&(*i.block), &DeghostMode::default()) {
                        Some(b) => {
                            i.block = Box::new(b);
                        },
                        None => {
                            empty_block(&mut i.block);
                        }
                    }
                },
                syn_verus::FnMode::Proof(_) => {
                    if has_return(&i.sig) {
                        default_return_block(&mut i.block);
                    } else {
                        empty_block(&mut i.block);
                    }
                }
                _ => {}
            }
            i.attrs = remove_proof_attr(&i.attrs);
            erase_ghost_sig(&mut i.sig.spec);
        } else {
            i.attrs = remove_proof_attr(&i.attrs);
        }
    }

    fn visit_trait_item_fn_mut(&mut self, i: &mut syn_verus::TraitItemFn) {
        if trait_fn_is_target(&i) {
            match i.sig.mode {
                syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default => {
                    if i.default.is_some() {
                        match remove_ghost_block(&(i.default.clone().unwrap()), &DeghostMode::default()) {
                            Some(b) => {
                                i.default = Some(b);
                            },
                            None => {
                                empty_block(&mut i.default.as_mut().unwrap());
                            }
                        }
                    }
                },
                syn_verus::FnMode::Proof(_) => {
                    if i.default.is_some() {
                        if has_return(&i.sig) {
                            default_return_block(&mut i.default.as_mut().unwrap());
                        } else {
                            empty_block(&mut i.default.as_mut().unwrap());
                        }
                    }
                }
                _ => {}
            }
            i.attrs = remove_proof_attr(&i.attrs);
            erase_ghost_sig(&mut i.sig.spec);
        } else {
            i.attrs = remove_proof_attr(&i.attrs);
        }
    }
}

pub fn erase_ghost_from_target(file: &mut syn_verus::File) {
    let erase_visitor = EraseGhostVisitor {};
    let mut macro_visitor = VerusMacroVisitor { visitor: erase_visitor };
    macro_visitor.visit_file_mut(file);
}
