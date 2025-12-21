use vstd::prelude::*;
fn main() {}
verus! {

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

#[verifier::external_body]
pub proof fn lemma_flatten_sets_union<A>(sets1: Set<Set<A>>, sets2: Set<Set<A>>)
    ensures
        flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
    unimplemented!()
}

pub proof fn lemma_flatten_sets_union_auto<A>()
    ensures
        forall|sets1: Set<Set<A>>, sets2: Set<Set<A>>| #[trigger]
            flatten_sets(sets1.union(sets2)) == flatten_sets(sets1).union(flatten_sets(sets2)),
{
}

} // verus!
