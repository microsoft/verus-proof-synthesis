use vstd::prelude::*;

fn main() {}

verus!{


pub proof fn commutativity_of_seq_map_and_filter<A, B>(s: Seq<A>, pred: spec_fn(A) -> bool, pred_on_mapped: spec_fn(B) -> bool, map: spec_fn(A) -> B)
    // ensure filter on original sequence is identical to filter on mapped sequence
    requires forall |i: int| 0 <= i < s.len() ==> #[trigger] pred(s[i]) == #[trigger] pred_on_mapped(map(s[i])),
    ensures s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map),
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        commutativity_of_seq_map_and_filter(subseq, pred, pred_on_mapped, map);
        assert(pred(s.last()) == pred_on_mapped(map(s.last())));
        assert(s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map)) by {
            assert(subseq.map_values(map).filter(pred_on_mapped) == subseq.filter(pred).map_values(map));
            assert(s.map_values(map) == subseq.map_values(map).push(map(s.last())));
            assert(s.map_values(map).drop_last() == subseq.map_values(map));
            if !pred(s.last()) {
                assert(s.map_values(map).filter(pred_on_mapped) == subseq.map_values(map).filter(pred_on_mapped)) by {
                    assert(subseq.map_values(map).filter(pred_on_mapped) == subseq.map_values(map).push(map(s.last())).filter(pred_on_mapped));
                }
            } else {
                // why this line the same as postcondition is required
                assert(s.map_values(map).filter(pred_on_mapped) == s.filter(pred).map_values(map));
            }
        }
    }
}

}
