use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A>
{
    // extra parens are for rust-analyzer
    Set::new(|a: A| (exists |s: Set<A>| sets.contains(s) && s.contains(a)))
}
#[verifier::spinoff_prover]

pub proof fn flatten_sets_spec<A>(sets: Set<Set<A>>)
    ensures
        (forall |e| #[trigger] flatten_sets(sets).contains(e) ==> exists |s| sets.contains(s) && s.contains(e)),
        (forall |s: Set<A>| #[trigger] sets.contains(s) ==> s.subset_of(flatten_sets(sets)))
{
}


}
