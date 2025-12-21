use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_set_map_insert<A, B>(s: Set<A>, f: spec_fn(A) -> B, x: A)
    ensures
        s.insert(x).map(f) == s.map(f).insert(f(x)),
{
}

} // verus!
