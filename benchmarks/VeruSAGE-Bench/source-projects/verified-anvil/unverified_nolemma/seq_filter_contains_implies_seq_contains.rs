use vstd::prelude::*;

fn main() {}

verus!{

/* Seq::filter is an opaque function in vstd. It needs to be revealed in the proof code */
pub proof fn seq_filter_contains_implies_seq_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, elt: A)
    requires s.filter(pred).contains(elt),
    ensures s.contains(elt)
{
    reveal(Seq::filter);
}

}
