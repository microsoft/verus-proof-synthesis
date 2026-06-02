use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_to_set_union_auto<A>()
    ensures
        forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set(),
{
}

} // verus!
