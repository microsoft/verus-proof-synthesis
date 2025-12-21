use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn some_differing_index_for_unequal_seqs<A>(s1: Seq<A>, s2: Seq<A>) -> (i: int)
    requires
        s1 != s2,
        s1.len() == s2.len(),
    ensures
        0 <= i < s1.len(),
        s1[i] != s2[i],
{
    proof_from_false() // TODO - replace with correct value
}

} // verus!
