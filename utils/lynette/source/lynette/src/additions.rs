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

fn mod_decl_is_equal(original: &syn_verus::ItemMod, changed: &syn_verus::ItemMod) -> bool {
    original.attrs == changed.attrs &&
    original.vis == changed.vis &&
    original.unsafety == changed.unsafety &&
    original.mod_token == changed.mod_token &&
    original.ident == changed.ident &&
    original.semi == changed.semi
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
                    println!("Disallowed changes made to impl block: {}", i_orig.self_ty.to_token_stream().to_string());
                    // println!("{:#?}", i_orig);
                    // println!("{:#?}", i_changed);
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
            (syn_verus::Item::Mod(m_orig), syn_verus::Item::Mod(m_changed)) => {
                if !mod_decl_is_equal(&m_orig, &m_changed) {
                    println!("Disallowed changes made to module declaration: {}", m_orig.ident.to_string());
                    return false;
                }

                match (&m_orig.content, &m_changed.content) {
                    (Some((orig_br, orig_items)), Some((changed_br, changed_items))) => {
                        if orig_br != changed_br {
                            println!("Disallowed changes made to module content braces: {}", m_orig.ident.to_string());
                            return false;
                        } else if !check_items(&orig_items[0..], &changed_items[0..]) {
                            return false;
                        } else {
                            idx_orig = idx_orig + 1;
                            idx_changed = idx_changed + 1;
                        }
                    },
                    (None, None) => {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    },
                    _ => {
                        println!("Disallowed changes made to module content: {}", m_orig.ident.to_string());
                        return false;
                    }
                }

            },
            (_, _) => {
                if original != changed {
                    println!("{:#?}", changed);
                    println!("{:#?}", original);
                    println!("{}", changed.to_token_stream().to_string());
                    println!("{}", original.to_token_stream().to_string());
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

            // original_verus_macros.iter().for_each(|m| {
            //     println!("{}", fprint_file(&m, Formatter::VerusFmt))
            // });

            // changed_verus_macros.iter().for_each(|m| {
            //     println!("{}", fprint_file(&m, Formatter::VerusFmt))
            // });

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

