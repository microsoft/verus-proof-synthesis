use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_subrange_subrange<A>(s: Seq<A>, start: int, midsize: int, endsize: int)
    requires
        0 <= start <= s.len(),
        0 <= midsize <= endsize <= s.len() - start,
    ensures
        s.subrange(start, start + endsize).subrange(0, midsize) == s.subrange(
            start,
            start + midsize,
        ),
{
}

} // verus!
