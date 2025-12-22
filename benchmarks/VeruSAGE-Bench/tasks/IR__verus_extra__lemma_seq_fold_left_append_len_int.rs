use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_append_len_int<A, B>(
    s: Seq<A>,
    prefix: Seq<B>,
    f: spec_fn(A) -> Seq<B>,
)
    ensures
        s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)).len() as int == s.fold_left(
            prefix.len() as int,
            |i: int, a: A| i + f(a).len() as int,
        ),
{
}

} // verus!
