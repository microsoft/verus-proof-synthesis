use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_to_set_distributes_over_addition<A>(s: Seq<A>, t: Seq<A>)
    ensures
        (s + t).to_set() == s.to_set() + t.to_set(),
{
}

} // verus!
