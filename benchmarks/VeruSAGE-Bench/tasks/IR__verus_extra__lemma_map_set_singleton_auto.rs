use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_map_set_singleton_auto<A, B>()
    ensures
        forall|x: A, f: spec_fn(A) -> B| #[trigger] set![x].map(f) == set![f(x)],
{
}

} // verus!
