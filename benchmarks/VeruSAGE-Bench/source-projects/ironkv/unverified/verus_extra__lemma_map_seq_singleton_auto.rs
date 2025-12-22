use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_map_seq_singleton_auto<A, B>()
    ensures
        forall|x: A, f: spec_fn(A) -> B| #[trigger] seq![x].map_values(f) =~= seq![f(x)],
{
}

} // verus!
