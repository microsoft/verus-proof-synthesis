This code is for benchmark cleanup, which should be run after the extraction script. Currently it does the following:
- reorders definitions in the file so that the target function appears last
- erases ghost code from the target function
- removes `use` statements for vstd, trying to prevent leakage of the usage of lemmas by the original proof (this is a hack, see TODOS.md for more)
- if using no lemma mode: removes all other proof fns in the code (except for those in traits)

To run the cleanup code, call it as in this script: `benchmarks\verified-storage\cleanup.sh`
