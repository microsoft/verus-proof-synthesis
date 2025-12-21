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

pub proof fn lemma_flatten_sets_insert<A>(sets: Set<Set<A>>, s: Set<A>)
    ensures flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s)
{
    assert_sets_equal!(flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s));
}


}
