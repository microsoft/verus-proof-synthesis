use vstd::prelude::*;
fn main() {}
verus! {

pub open spec fn flatten_sets<A>(sets: Set<Set<A>>) -> Set<A> {
    Set::new(|a: A| (exists|s: Set<A>| sets.contains(s) && s.contains(a)))
}

pub proof fn flatten_sets_spec<A>(sets: Set<Set<A>>)
    ensures
        (forall|e| #[trigger]
            flatten_sets(sets).contains(e) ==> exists|s| sets.contains(s) && s.contains(e)),
        (forall|s: Set<A>| #[trigger] sets.contains(s) ==> s.subset_of(flatten_sets(sets))),
{
}

} // verus!
