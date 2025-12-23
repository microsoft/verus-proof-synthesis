use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
pub proof fn lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires forall |i: int| 0 <= i && i < s.len() ==> pred(s[i])
    ensures  s.filter(pred) == s
    decreases s.len()
{
    reveal(Seq::filter);
    if s.len() != 0 {
        let subseq = s.drop_last();
        lemma_if_everything_in_seq_satisfies_filter_then_filter_is_identity(subseq, pred);
        assert_seqs_equal!(s, subseq.push(s.last()));
    }
}


}
