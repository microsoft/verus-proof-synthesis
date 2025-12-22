use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_sum_len_int_positive<A, B>(
    s: Seq<A>,
    low: nat,
    f: spec_fn(A) -> Seq<B>,
)
    ensures
        s.fold_left(low as int, |acc: int, x: A| acc + f(x).len()) >= 0,
{
}

} // verus!
