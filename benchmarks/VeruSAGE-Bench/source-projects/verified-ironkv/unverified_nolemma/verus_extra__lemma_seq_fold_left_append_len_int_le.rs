use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(
    s: Seq<A>,
    i: int,
    low: int,
    f: spec_fn(A) -> Seq<B>,
)
    requires
        0 <= i <= s.len() as int,
        0 <= low,
    ensures
        s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
        s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <= s.fold_left(
            low,
            |acc: int, x: A| acc + f(x).len(),
        ),
{
}

} // verus!
