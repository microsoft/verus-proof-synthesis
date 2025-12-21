use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_sum_le<A>(s: Seq<A>, init: int, high: int, f: spec_fn(A) -> int)
    requires
        forall|i: int| 0 <= i < s.len() ==> f(s[i]) <= high,
    ensures
        s.fold_left(init, |acc: int, x: A| acc + f(x)) <= init + s.len() * high,
{
}

} // verus!
