use vstd::prelude::*;
use std::collections;
use vstd::bytes::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
pub proof fn lemma_filter_skip_rejected<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i <= s.len(),
        forall |j| 0 <= j < i ==> !pred(s[j]),
    ensures
        s.filter(pred) == s.skip(i).filter(pred)
    decreases
        s.len()
{
    reveal(Seq::filter);
    if s.len() == 0 {
        assert(s.skip(i) =~= s);
    }
    else if i < s.len() {
        assert(s.skip(i).drop_last() =~= s.drop_last().skip(i));
        lemma_filter_skip_rejected(s.drop_last(), pred, i);
    }
    else {
        assert(s.skip(i) =~= s.drop_last().skip(i - 1));
        lemma_filter_skip_rejected(s.drop_last(), pred, i - 1);
    }
}


}
