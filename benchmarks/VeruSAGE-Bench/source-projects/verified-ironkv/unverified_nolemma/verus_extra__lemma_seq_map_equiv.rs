use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_map_equiv<A, B>(f: spec_fn(A) -> B, g: spec_fn(int, A) -> B)
    requires
        forall|i: int, a: A| #[trigger] g(i, a) == f(a),
    ensures
        forall|s: Seq<A>| s.map_values(f) == s.map(g),
{
}

} // verus!
