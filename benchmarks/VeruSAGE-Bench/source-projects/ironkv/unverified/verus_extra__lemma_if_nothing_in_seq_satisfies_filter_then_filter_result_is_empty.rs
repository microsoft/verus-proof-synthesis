use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_if_nothing_in_seq_satisfies_filter_then_filter_result_is_empty<A>(
    s: Seq<A>,
    pred: spec_fn(A) -> bool,
)
    requires
        forall|i: int| 0 <= i && i < s.len() ==> !pred(s[i]),
    ensures
        s.filter(pred) =~= Seq::<A>::empty(),
{
}

} // verus!
