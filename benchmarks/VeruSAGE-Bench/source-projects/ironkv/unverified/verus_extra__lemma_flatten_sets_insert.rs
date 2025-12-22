use vstd::prelude::*;
fn main() {}
verus! {

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

pub proof fn lemma_flatten_sets_insert<A>(sets: Set<Set<A>>, s: Set<A>)
    ensures
        flatten_sets(sets.insert(s)) == flatten_sets(sets).union(s),
{
}

} // verus!
