Here are a list of outstanding items that we need to fix for benchmark gen. This relates to both this script and Shan's extraction script. There are some bugs in this script and also issues with the overall flow.

Currently these items require manual fix after running the script...

In the verified-memory-allocator, verified-storage, and verified-ironkv benchmark directories, I also tried to document all of the manual fixups I had to do, so it would be good to cross-check with those in the future.

### Reordering target proof to the last item

Ideally, the target fn is the last item in the file. There are currently a few issues.

- From the current extraction output, sometimes there are multiple functions that don't have `unimplemented!()` as the body. This messes up the file reordering - this script treats any proof or exec function whose body is not `unimplemented!()` as the target fn and will order it last. Perhaps once the extraction and cleanup scripts are merged to one script, this will not be an issue. Note: our eventual solution should probably be robust to the scenario where non-target functions do have a body that is not `unimplemented!()`, in case we want to test this.
- This script gets the ordering quite wrong for the verified-storage benchmarks. I haven't yet had time to debug why.

### Ordering for all definitions

Currently: the extraction script will group all definitions from a file together, and those are in the order they appear in the file (I think?). Then, the files are ordered alphabetically (I think?).

Ideally: order files in order of dependency hierarchy. I think the current approach of ordering the definitions from a single file from top to bottom makes sense.

This is only "nice to have", it doesn't have any implications for cheating.

### `use` statements for lemma dependencies in original proof - potential cheating

In extraction, we should first erase the proof for the target function, and then extract the dependencies, and then figure out what `use` statements are actually needed.

The issue arises when we need spec definitions from vstd:: …, versus when the original proof uses lemmas from vstd:: … . We shouldn't include the import in the latter case since that would be cheating.

The current cleanup script uses a hardcoded solution to keep the imports from the projects we have studied that have spec fns. This is an attempt to try to prevent leakage of any vstd lemmas used in the original proof.

### #[verifier::opaque] spec fns - potential cheating

Currently: If a spec fn definition is not used in the original proof, then I think the body is not extracted by the extraction script - it is replaced with external_body and unimplemented!(). This is cheating, since it leaks the fact that the body is not necessary for the proof.

Also, if the definition *is* revealed in the original proof, then it seems #[verifier::opaque] is dropped by the extraction.

### Code with `Ghost(…)` and `Tracked(…)` is not erased by current lynette ghost cleanup - potential cheating

The tool does not classify capital-G and capital-T `Ghost` and `Tracked` as proof code, so it doesn't erase them. Note: it does seem to classify  `ghost` and `tracked` correctly.

Note from Chris: `Ghost` and `Tracked` are parsed either as patterns or as function calls. Would need special handling to erase.

If the expression is needed, we should replace a pattern `Ghost(x)` or `Tracked(x)` with `Ghost(_)`, and we should replace a function argument/return value `Ghost(x)` with `Ghost(arbitrary())` and `Tracked(x)` with `Tracked(proof_from_false())`.

**Note:** There are also some problems with the current safety check due to the same issue. Right now, a change `my_exec_func(Ghost(arbitrary()))` to `my_exec_func(Ghost(Set::empty()))` will be rejected, because the safety check also does not know that capital-G `Ghost` is ghost code, so it thinks the LLM is changing exec code. In my manual fixup, my solution is to do this:

```
let ghost arg_ghost0: Set<T> = arbitrary();
my_exec_func(Ghost(arg_ghost0));
```

Then the LLM can change the `let ghost ...` line and not have to change the `my_exec_func` line, and it will be classified as safe since the safety check correctly classifies `ghost`. However, I don't know how often the LLM actually obeys this rule, since we don't instruct it specifically to only change the `let ghost ...`, so a lot of "valid" changes might be getting rejected as unsafe right now. The better solution is to classify `Ghost` correctly.

### Other bugs in ghost erasure

Other bugs in the cleanup script regarding ghost code erasure. Unfortunately I lost the original files so I can't give examples :( But we could try to write test cases to reproduce the bugs.
- Incorrectly erases entire if statement. I think the if body had `let ghost...` inside of it.
- Misses `let ghost...` in match arm statement.
The ghost erasure is inherited from the lynette tool from last year, we may need to review it more closely to double check the logic.

### Remove "broadcast use" - potential cheating

This is currently not removed by the extraction.

### Handling traits
- Proof fns in traits should be treated as axioms: we should always include them when the target fn depends on the trait.
- Right now we don't extract the proof fn if it is not used in the original proof: if we consider these as axioms, then this is cheating, since it leaks the fact that the axiom is not necessary.

### Other axiom detection

Should any proof fn marked as "axiom" or "external_body" etc. be considered an axiom? How to tell when to include? Note: we could set this manually, since a user would configure their axioms themselves.

Examples of proof fns that could be axioms:
- axiom
- external_body
- admit!()
- assume(false);
- Also be aware of: external_fn_specification, external_trait_specification, when the relevant items are used

Note: the current cleanup script does not support axiom detection, so it will erase them, and they have to be manually added back.

### Extra definitions / missing definitions

Per discussion with Shan, the current extraction seems to miss some definitions, and so some definitions were manually added, but they aren't always necessary. Examples from delegation_map in ironkv.

### auto_ext_equal

The benchmark gen should automatically add `#[verifier::auto_ext_equal(assert, assert_by, ensures)]` to the top of the file (todo: where exactly does this need to go?). Currently this is just added manually.

### Rewriting return statements

For exec functions that return complex expressions and not just a variable, we observed that it is better to have the code look like `let res = expr; res`, rather than just return `expr` directly, so that the model can write assert statements directly on the variable `res`. It seems that the LLM often rewrites to this form itself, and this change would be rejected as unsafe. Currently, I just manually changed the files to match this format.
