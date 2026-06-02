use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn set_map_union_auto<A, B>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, f: spec_fn(A) -> B| #[trigger]
            (s1 + s2).map(f) == s1.map(f) + s2.map(f),
{
}

} // verus!
