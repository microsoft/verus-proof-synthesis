use vstd::prelude::*;

fn main() {}

verus!{

proof fn seq_pred_false_on_all_elements_implies_empty_filter<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |e: A| #![auto] s.contains(e) ==> !pred(e),
    ensures s.filter(pred).len() == 0,
    decreases s.len()
    // If `pred` is false on every element, filter will return an empty sequence.
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        // prove precondition for subseq and recursive call
        assert(forall |e: A| subseq.contains(e) ==> !pred(e)) by {
            assert(forall |i: int| 0 <= i < subseq.len() ==> s.contains(#[trigger] s[i]) ==> !pred(subseq[i]));
        }
        seq_pred_false_on_all_elements_implies_empty_filter(subseq, pred);
        assert(subseq.filter(pred) == s.filter(pred)) by {
            assert(!pred(s.last())) by {
                assert(s.contains(s.last()) ==> !pred(s.last()));
            };
        } // s.filter(pred) == subseq.filter(pred) == ... == Seq::empty()
    }
}

}
