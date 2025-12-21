use vstd::prelude::*;
fn main() {}
verus! {

pub open spec fn flatten_set_seq<A>(sets: Seq<Set<A>>) -> Set<A> {
    sets.fold_left(Set::<A>::empty(), |s1: Set<A>, s2: Set<A>| s1.union(s2))
}

pub proof fn lemma_flatten_set_seq_spec<A>(sets: Seq<Set<A>>)
    ensures
        (forall|x: A| #[trigger]
            flatten_set_seq(sets).contains(x) ==> exists|i: int|
                0 <= i < sets.len() && #[trigger] sets[i].contains(x)),
        (forall|x: A, i: int|
            0 <= i < sets.len() && #[trigger] sets[i].contains(x) ==> flatten_set_seq(
                sets,
            ).contains(x)),
{
}

} // verus!
