// I don't have access to all the testing files so I just moved it here and mark as obsolete...

use std::path::PathBuf;
use lynette::{check_allowed_additions_only, Error};

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
