use std::path::PathBuf;
use quote::ToTokens;
use crate::{utils::*, DeghostMode};
use crate::deghost::{remove_ghost_block, remove_verus_macro, remove_ghost_sig};
use syn_verus::FnMode::*;

/*
Checks whether attribute contains instructions about completing a proof
*/
fn is_proof_attr(attr: &syn_verus::Attribute) -> bool {
    attr.path().segments.len() > 1
    && attr.path().segments[0].ident.to_string() == "verifier"
    && (attr.path().segments[1].ident.to_string() == "rlimit"
        || attr.path().segments[1].ident.to_string() == "integer_ring"
        || attr.path().segments[1].ident.to_string() == "memoize"
        || attr.path().segments[1].ident.to_string() == "loop_isolation"
        || attr.path().segments[1].ident.to_string() == "spinoff_prover")
}

pub fn remove_proof_attr(attr: &Vec<syn_verus::Attribute>) -> Vec<syn_verus::Attribute> {
    attr.iter().filter(|a| !is_proof_attr(a)).map(|a| a.clone()).collect()
}

/*
Erases all ghost code from exec fn only. Leaves all other fn types unchanged.
*/
fn remove_ghost_from_exec_fn(func: &syn_verus::ItemFn) -> syn_verus::ItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            match remove_ghost_block(&(*func.block), &DeghostMode::default()) {
                Some(new_block) => {
                    syn_verus::ItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: Box::new(new_block), // Box the new block
                        semi_token: func.semi_token.clone(),
                    }
                },
                None => {
                    syn_verus::ItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: Box::new(syn_verus::Block { brace_token: func.block.brace_token.clone(), stmts: Vec::new() }), // empty block
                        semi_token: func.semi_token.clone(),
                    }
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn remove_ghost_from_impl_exec_fn(func: &syn_verus::ImplItemFn) -> syn_verus::ImplItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            match remove_ghost_block(&func.block, &DeghostMode::default()) {
                Some(new_block) => {
                    syn_verus::ImplItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        defaultness: func.defaultness.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: new_block,
                        semi_token: func.semi_token.clone(),
                    }
                },
                None => {
                    syn_verus::ImplItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        defaultness: func.defaultness.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: syn_verus::Block { brace_token: func.block.brace_token.clone(), stmts: Vec::new() }, // empty block
                        semi_token: func.semi_token.clone(),
                    }
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn remove_ghost_from_trait_exec_fn(func: &syn_verus::TraitItemFn) -> syn_verus::TraitItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            if func.default.is_some() {
                match remove_ghost_block(&(func.default.clone().unwrap()), &DeghostMode::default()) {
                    Some(new_block) => {
                        syn_verus::TraitItemFn {
                            attrs: remove_proof_attr(&func.attrs),
                            sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                            default: Some(new_block),
                            semi_token: func.semi_token.clone(),
                        }
                    },
                    None => {
                        syn_verus::TraitItemFn {
                            attrs: remove_proof_attr(&func.attrs),
                            sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                            default: None, // empty block
                            semi_token: func.semi_token.clone(),
                        }
                    }
                }
            } else {
                syn_verus::TraitItemFn {
                    attrs: remove_proof_attr(&func.attrs),
                    sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                    default: None, // empty block
                    semi_token: func.semi_token.clone(),
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn check_fn_signature(original: &syn_verus::Signature, changed: &syn_verus::Signature) -> bool {
    let mut orig_spec = original.spec.clone();
    orig_spec.prover = None;
    orig_spec.decreases = None;
    orig_spec.invariants = None;
    let mut changed_spec = changed.spec.clone();
    changed_spec.prover = None;
    changed_spec.decreases = None;
    changed_spec.invariants = None;
    remove_ghost_sig(original, &DeghostMode::default()) == remove_ghost_sig(changed, &DeghostMode::default())
    && orig_spec == changed_spec
}

fn check_impl_items(original_items: &[syn_verus::ImplItem], changed_items: &[syn_verus::ImplItem]) -> bool {
    let mut idx_orig = 0;
    let mut idx_changed = 0;
    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::ImplItem::Fn(f_orig), syn_verus::ImplItem::Fn(f_changed)) => {
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && fn_body_is_target(&f_orig.block) && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    match f_changed.sig.mode {
                        Proof(_) => {
                            if f_orig.vis != f_changed.vis {
                                println!("Disallowed changes in the visibility of proof function: {}", myfun);
                                println!(" Original visibility: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed visibility: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else if remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs) {
                                println!("Disallowed changes in the attributes of proof function: {}", myfun);
                                println!(" Original attributes: {:?}", f_orig.attrs);
                                println!(" Changed attributes: {:?}\n", f_changed.attrs);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                println!("Disallowed changes in the signature (e.g., requires, ensures) of a proof function:");
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}\n", f_changed.sig.to_token_stream().to_string());

                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_impl_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_impl_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if deghosted_orig != deghosted_changed {
                                println!("Unsafe change detected in the body of executable function: {}", myfun);
                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {
                                println!("Disallowed changes made to the signature of executable function: {}", myfun);
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                println!("Disallowed addition to the program: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (_, syn_verus::ImplItem::Macro(_)) => {
                // check exact match
                if original != changed {
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, _) => {
                // all other items must have exact match
                if original != changed {
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

fn check_trait_items(original_items: &[syn_verus::TraitItem], changed_items: &[syn_verus::TraitItem]) -> bool {
    let mut idx_orig = 0;
    let mut idx_changed = 0;

    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::TraitItem::Fn(f_orig), syn_verus::TraitItem::Fn(f_changed)) => {

                // Get the string name of f_orig
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && f_orig.default.is_some() && fn_body_is_target(&f_orig.default.clone().unwrap())
                    && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    match f_changed.sig.mode {
                        Proof(_) => {
                            if !(remove_proof_attr(&f_orig.attrs) == remove_proof_attr(&f_changed.attrs) && check_fn_signature(&f_orig.sig, &f_changed.sig)) {
                                println!("Disallowed changes detected for a trait-proof function: {}", myfun);
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_trait_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_trait_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if !(deghosted_orig == deghosted_changed && check_fn_signature(&f_orig.sig, &f_changed.sig)) {
                                println!("Disallowed changes detected for a trait-executable function: {}", myfun);
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (_, syn_verus::TraitItem::Macro(_)) => {
                // check exact match
                if original != changed {
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, _) => {
                // all other items must have exact match
                if original != changed {
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

fn check_items(original_items: &[syn_verus::Item], changed_items: &[syn_verus::Item]) -> bool
{
    let mut idx_orig = 0;
    let mut idx_changed = 0;

    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::Item::Fn(f_orig), syn_verus::Item::Fn(f_changed)) => {

                // Get the string name of f_orig
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                let mynewsig = f_changed.sig.to_token_stream().to_string();
                let mut mynewfun = mynewsig.clone();
                if let Some(mynewindex) = mynewsig.find(')') {
                   mynewfun = (&mynewsig[..=mynewindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && fn_body_is_target(&*f_orig.block) && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    match f_changed.sig.mode {
                        Proof(_) => {
                            if f_orig.vis != f_changed.vis {
                                println!("Disallowed changes in the visibility of proof function: {}", myfun);
                                println!(" Original visibility: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed visibility: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else if remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs) {
                                println!("Disallowed changes in the attributes of proof function: {}", myfun);
                                println!(" Original attributes: {:?}", f_orig.attrs);
                                println!(" Changed attributes: {:?}", f_changed.attrs);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                println!("Disallowed changes found in the signature (e.g., requires, ensures) of a proof function:");
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if deghosted_orig != deghosted_changed {

                                // Print out error information
                                println!("Disallowed changes found in the body of function: {}", myfun);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                // Print out error information
                                println!("Disallowed changes found in an executable function's requires/ensures conditions");
                                println!("\tOriginal signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!("\tChanged  signature: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                println!("Disallowed addition of a new function: {}", mynewfun);
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (syn_verus::Item::Impl(i_orig), syn_verus::Item::Impl(i_changed)) => {
                // exact match for everything besides verifier attrs
                let mut orig_clone = i_orig.clone();
                orig_clone.items = Vec::new();
                orig_clone.attrs = remove_proof_attr(&orig_clone.attrs);
                let mut changed_clone = i_changed.clone();
                changed_clone.items = Vec::new();
                changed_clone.attrs = remove_proof_attr(&changed_clone.attrs);
                // check exact match, then check child items
                if orig_clone != changed_clone {
                    return false;
                } else if !check_impl_items(&i_orig.items[0..], &i_changed.items[0..]) {
                    return false;
                }
                else {
                    // then advance to next item
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (syn_verus::Item::Trait(t_orig), syn_verus::Item::Trait(t_changed)) => {
                // exact match for everything besides verifier attrs
                let mut orig_clone = t_orig.clone();
                orig_clone.items = Vec::new();
                orig_clone.attrs = remove_proof_attr(&orig_clone.attrs);
                let mut changed_clone = t_changed.clone();
                changed_clone.items = Vec::new();
                changed_clone.attrs = remove_proof_attr(&changed_clone.attrs);
                // check exact match, then check child items
                if !(orig_clone == changed_clone && check_trait_items(&t_orig.items[0..], &t_changed.items[0..])) {
                    return false;
                } else {
                    // then advance to next item
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, syn_verus::Item::Use(_)) | (_, syn_verus::Item::Macro(_)) | (_, syn_verus::Item::BroadcastUse(_)) => {
                // check exact match
                if original != changed {
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, _) => {
                if original != changed {
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

/*
Safety check rules:
- we can add new spec fns or proof fns
- we cannot change existing spec, proof, or exec fns -- EXCEPT the target function
- we cannot change the signature of the target function, except to add decreases, opens invariants, or prover clause
- we cannot change exec code in the body of the target function
- the target function is identified by being a proof or exec fn whose body does not contain `unimplemented!()`.
    all other proof and exec fn will have a body with `unimplemented!()`
*/
pub fn check_allowed_additions_only(original_file: PathBuf, changed_file: PathBuf) -> Result<bool, Error> {
    let original = fload_file(&original_file)?;
    let changed = fload_file(&changed_file)?;

    let original_pure_file = remove_verus_macro(&original);
    let changed_pure_file = remove_verus_macro(&changed);

    if !check_items(&original_pure_file.items[0..], &changed_pure_file.items[0..]) {
        return Ok(false);
    }

    extract_verus_macro(&original).and_then(|original_verus_macros| {
        extract_verus_macro(&changed).and_then(|changed_verus_macros| {

            if original_verus_macros.len() != changed_verus_macros.len() {
                println!("Disallowed changes made to Verus macros in the original files.");
                return Ok(false);
            }

            for i in 0..original_verus_macros.len() {
                if !check_items(&original_verus_macros[i].items[0..], &changed_verus_macros[i].items[0..]) {
                    println!("Disallowed changes made to Verus macros in the original files.");
                    return Ok(false);
                }
            }

            Ok(true)
        })
    })
}

#[cfg(test)]
mod additions_tests {
    use super::*;

    const BASE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\base_lemma.rs";
    const LEMMA_ADD_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_lemma.rs";
    const LEMMA_ADD_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_spec.rs";
    const LEMMA_ADD_USE: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_use.rs";
    const LEMMA_ADD_CONST: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_const.rs";
    const LEMMA_ADD_MACRO: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_macro.rs";
    const LEMMA_ADD_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_add_exec.rs";
    const LEMMA_CHANGE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_lemma.rs";
    const LEMMA_CHANGE_LEMMA_REQUIRES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_lemma_requires.rs";
    const LEMMA_CHANGE_LEMMA_ENSURES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_lemma_ensures.rs";
    const LEMMA_CHANGE_LEMMA_ATTR: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_lemma_attr.rs";
    const LEMMA_CHANGE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_spec.rs";
    const LEMMA_CHANGE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_exec.rs";
    const LEMMA_CHANGE_TARGET_PROOF: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_target_proof.rs";
    const LEMMA_CHANGE_TARGET_PROOF_NAME: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_target_proof_name.rs";
    const LEMMA_CHANGE_LEMMA_DECREASES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_change_lemma_decreases.rs";
    const LEMMA_REMOVE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_remove_lemma.rs";
    const LEMMA_REMOVE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_remove_spec.rs";
    const LEMMA_REMOVE_USE: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_remove_use.rs";
    const LEMMA_REMOVE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_remove_exec.rs";
    const LEMMA_REMOVE_TARGET: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\lemma_remove_target.rs";

    const BASE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\base_exec.rs";
    const EXEC_CHANGE_REQUIRES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_change_requires.rs";
    const EXEC_CHANGE_ENSURES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_change_ensures.rs";
    const EXEC_CHANGE_DECREASES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_change_decreases.rs";
    const EXEC_ADD_ASSERT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_add_assert.rs";
    const EXEC_ADD_ASSERT_FORALL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_add_assert_forall.rs";
    const EXEC_ADD_INVARIANT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_add_invariant.rs";
    const EXEC_ADD_LEMMA_CALL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_add_lemma_call.rs";
    const EXEC_CHANGE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\exec_change_exec.rs";

    const BASE_TRAIT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\base_trait.rs";
    const TRAIT_ADD_ASSERT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_add_assert.rs";
    const TRAIT_ADD_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_add_spec.rs";
    const TRAIT_ADD_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_add_lemma.rs";
    const TRAIT_ADD_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_add_exec.rs";
    const TRAIT_CHANGE_ENSURES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_ensures.rs";
    const TRAIT_CHANGE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_exec.rs";
    const TRAIT_CHANGE_GENERICS: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_generics.rs";
    const TRAIT_CHANGE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_lemma.rs";
    const TRAIT_CHANGE_NAME: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_name.rs";
    const TRAIT_CHANGE_REQUIRES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_requires.rs";
    const TRAIT_CHANGE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_change_spec.rs";
    const TRAIT_REMOVE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_remove_spec.rs";
    const TRAIT_REMOVE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\trait_remove_lemma.rs";

    const BASE_IMPL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\base_impl.rs";
    const IMPL_ADD_ASSERT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_add_assert.rs";
    const IMPL_ADD_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_add_spec.rs";
    const IMPL_ADD_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_add_lemma.rs";
    const IMPL_ADD_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_add_exec.rs";
    const IMPL_CHANGE_ENSURES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_exec.rs";
    const IMPL_CHANGE_EXEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_ensures.rs";
    const IMPL_CHANGE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_lemma.rs";
    const IMPL_CHANGE_REQUIRES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_requires.rs";
    const IMPL_CHANGE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_spec.rs";
    const IMPL_CHANGE_NAME: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_change_name.rs";
    const IMPL_REMOVE_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_remove_lemma.rs";
    const IMPL_REMOVE_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\impl_remove_spec.rs";

    const ATTR_RLIMIT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_rlimit.rs";
    const ATTR_RLIMIT_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_rlimit_removed.rs";
    const ATTR_EXT_EQUAL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_ext_equal.rs";
    const ATTR_EXT_EQUAL_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_ext_equal_removed.rs";
    const ATTR_EXTERNAL_BODY_PAREN: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_body_paren.rs";
    const ATTR_EXTERNAL_BODY_PAREN_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_body_paren_removed.rs";
    const ATTR_EXTERNAL_BODY: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_body.rs";
    const ATTR_EXTERNAL_BODY_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_body_removed.rs";
    const ATTR_EXTERNAL_FN_SPECIFICATION: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_fn_specification.rs";
    const ATTR_EXTERNAL_FN_SPECIFICATION_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_fn_specification_removed.rs";
    const ATTR_EXTERNAL_TRAIT_SPECIFICATION: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_trait_specification.rs";
    const ATTR_EXTERNAL_TRAIT_SPECIFICATION_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_external_trait_specification_removed.rs";
    const ATTR_INLINE: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_inline.rs";
    const ATTR_INLINE_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_inline_removed.rs";
    const ATTR_INTEGER_RING_PAREN: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_integer_ring_paren.rs";
    const ATTR_INTEGER_RING_PAREN_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_integer_ring_paren_removed.rs";
    const ATTR_INTEGER_RING: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_integer_ring.rs";
    const ATTR_INTEGER_RING_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_integer_ring_removed.rs";
    const ATTR_LOOP_ISOLATION: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_loop_isolation.rs";
    const ATTR_LOOP_ISOLATION_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_loop_isolation_removed.rs";
    const ATTR_MEMOIZE: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_memoize.rs";
    const ATTR_MEMOIZE_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_memoize_removed.rs";
    const ATTR_OPAQUE: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_opaque.rs";
    const ATTR_OPAQUE_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_opaque_removed.rs";
    const ATTR_REJECT_RECURSIVE_TYPES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_reject_recursive_types.rs";
    const ATTR_REJECT_RECURSIVE_TYPES_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_reject_recursive_types_removed.rs";
    const ATTR_SPINOFF_PROVER: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_spinoff_prover.rs";
    const ATTR_SPINOFF_PROVER_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_spinoff_prover_removed.rs";
    const ATTR_WHEN_USED_AS_SPEC: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_when_used_as_spec.rs";
    const ATTR_WHEN_USED_AS_SPEC_REMOVED: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_additions\\attr\\attr_when_used_as_spec_removed.rs";

    #[test]
    fn test_lemma_add_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_add_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_add_use() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_USE);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_add_const() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_CONST);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_add_macro() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_MACRO);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_add_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_ADD_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_lemma_attr() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_LEMMA_ATTR);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_lemma_requires() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_LEMMA_REQUIRES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_lemma_ensures() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_LEMMA_ENSURES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_target_proof() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_TARGET_PROOF);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_change_target_proof_name() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_TARGET_PROOF_NAME);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_change_lemma_decreases() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_CHANGE_LEMMA_DECREASES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_lemma_remove_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_REMOVE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_remove_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_REMOVE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_remove_use() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_REMOVE_USE);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_remove_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_REMOVE_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_lemma_remove_target() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_LEMMA);
        let changed = PathBuf::from(LEMMA_REMOVE_TARGET);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_exec_change_requires() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_CHANGE_REQUIRES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_exec_change_ensures() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_CHANGE_ENSURES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_exec_change_decreases() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_CHANGE_DECREASES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_exec_add_lemma_call() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_ADD_LEMMA_CALL);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_exec_add_assert() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_ADD_ASSERT);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_exec_add_assert_forall() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_ADD_ASSERT_FORALL);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_exec_add_invariant() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_ADD_INVARIANT);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_exec_change_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_EXEC);
        let changed = PathBuf::from(EXEC_CHANGE_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_add_assert() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_ADD_ASSERT);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_trait_add_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_ADD_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_trait_add_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_ADD_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_trait_add_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_ADD_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_ensures() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_ENSURES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_generics() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_GENERICS);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_name() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_NAME);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_requires() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_REQUIRES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_change_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_CHANGE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_remove_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_REMOVE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_trait_remove_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_TRAIT);
        let changed = PathBuf::from(TRAIT_REMOVE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_add_assert() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_ADD_ASSERT);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_impl_add_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_ADD_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_impl_add_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_ADD_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_impl_add_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_ADD_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_ensures() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_ENSURES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_exec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_EXEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_name() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_NAME);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_requires() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_REQUIRES);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_change_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_CHANGE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_remove_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_REMOVE_LEMMA);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_impl_remove_spec() -> Result<(), Error> {
        let orig = PathBuf::from(BASE_IMPL);
        let changed = PathBuf::from(IMPL_REMOVE_SPEC);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_rlimit() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_RLIMIT);
        let changed = PathBuf::from(ATTR_RLIMIT_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_ext_equal() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_EXT_EQUAL);
        let changed = PathBuf::from(ATTR_EXT_EQUAL_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_external_body() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_EXTERNAL_BODY);
        let changed = PathBuf::from(ATTR_EXTERNAL_BODY_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_external_body_paren() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_EXTERNAL_BODY_PAREN);
        let changed = PathBuf::from(ATTR_EXTERNAL_BODY_PAREN_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_external_fn_specification() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_EXTERNAL_FN_SPECIFICATION);
        let changed = PathBuf::from(ATTR_EXTERNAL_FN_SPECIFICATION_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_external_trait_specification() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_EXTERNAL_TRAIT_SPECIFICATION);
        let changed = PathBuf::from(ATTR_EXTERNAL_TRAIT_SPECIFICATION_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_inline() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_INLINE);
        let changed = PathBuf::from(ATTR_INLINE_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_integer_ring_paren() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_INTEGER_RING_PAREN);
        let changed = PathBuf::from(ATTR_INTEGER_RING_PAREN_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_integer_ring() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_INTEGER_RING);
        let changed = PathBuf::from(ATTR_INTEGER_RING_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_loop_isolation() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_LOOP_ISOLATION);
        let changed = PathBuf::from(ATTR_LOOP_ISOLATION_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_memoize() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_MEMOIZE);
        let changed = PathBuf::from(ATTR_MEMOIZE_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_opaque() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_OPAQUE);
        let changed = PathBuf::from(ATTR_OPAQUE_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_reject_recursive_types() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_REJECT_RECURSIVE_TYPES);
        let changed = PathBuf::from(ATTR_REJECT_RECURSIVE_TYPES_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }

    #[test]
    fn test_attr_spinoff_prover() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_SPINOFF_PROVER);
        let changed = PathBuf::from(ATTR_SPINOFF_PROVER_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, true);
        Ok(())
    }

    #[test]
    fn test_attr_when_used_as_spec() -> Result<(), Error> {
        let orig = PathBuf::from(ATTR_WHEN_USED_AS_SPEC);
        let changed = PathBuf::from(ATTR_WHEN_USED_AS_SPEC_REMOVED);
        assert_eq!(check_allowed_additions_only(orig, changed)?, false);
        Ok(())
    }
}
