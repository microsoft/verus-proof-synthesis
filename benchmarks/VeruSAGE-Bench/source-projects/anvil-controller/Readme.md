Benchmarks in this folder originate from the verified ```vreplicaset``` controller in [Anvil](https://github.com/anvil-verifier/anvil/).

All executable or proof functions in [```vreplicaset``` controller](https://github.com/anvil-verifier/anvil/tree/main/src/controllers/vreplicaset_controller) that requires proof annotations were extracted and put here with one exception:

The following 5 functions were initially extracted, but excluded at a later stage of benchmark preparation as they have deps_hack dependency.

```
vreplicaset_controller/exec/reconciler.rs filter_pods
vreplicaset_controller/exec/reconciler.rs make_owner_references
vreplicaset_controller/exec/reconciler.rs objects_to_pods
vreplicaset_controller/exec/reconciler.rs reconcile_core-fixed
vreplicaset_controller/proof/helper_lemmas.rs lemma_filtered_pods_set_equals_matching_pods
```

Many thanks to the Anvil authors who kindly explained to us the structure of Anvil, demonstrated how to compile and verify the original Anvil project, and suggested us to focus on the ```vreplicaset``` controller.
