use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
            == s.fold_left(low, |b: int, a: A| b + f(a)),
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_len_int_positive<A, B>(
    s: Seq<A>,
    low: nat,
    f: spec_fn(A) -> Seq<B>,
)
    ensures
        s.fold_left(low as int, |acc: int, x: A| acc + f(x).len()) >= 0,
    decreases s.len(),
{
    unimplemented!()
}

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
