use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_push_to_set<A>(s: Seq<A>, x: A)
    ensures
        s.push(x).to_set() == s.to_set().insert(x),
{
}

} // verus!
