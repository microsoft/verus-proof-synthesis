use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::external_body]
pub proof fn lemma_to_set_distributes_over_addition<A>(s: Seq<A>, t: Seq<A>)
    ensures
        (s + t).to_set() == s.to_set() + t.to_set(),
{
    unimplemented!()
}

pub proof fn lemma_to_set_union_auto<A>()
    ensures
        forall|s: Seq<A>, t: Seq<A>| #[trigger] (s + t).to_set() == s.to_set() + t.to_set(),
{
}

} // verus!
