use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn seq_map_values_concat<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B)
    ensures
        (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f),
{
}

} // verus!
