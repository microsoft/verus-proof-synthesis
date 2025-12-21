use vstd::prelude::*;

fn main() {}

verus!{

/* Seq::filter is an opaque spec function in vstd. It needs to be revealed in the proof code */

proof fn seq_pred_false_on_all_elements_implies_empty_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |e: A| #![auto] s.contains(e) ==> !pred(e),
    ensures s.filter(pred).len() == 0,
{
    reveal(Seq::filter);
}

}
