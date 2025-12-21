use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_add_subrange<A>(s: Seq<A>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= s.len(),
    ensures
        s.subrange(i, j) + s.subrange(j, k) == s.subrange(i, k),
{
}

} // verus!
