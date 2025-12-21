use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_to_set_singleton_auto<A>()
    ensures
        forall|x: A| #[trigger] seq![x].to_set() == set![x],
{
}

} // verus!
