use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
            == s.fold_left(low, |b: int, a: A| b + f(a)),
{
}

} // verus!
