use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_seq_fold_left_append_right<A, B>(
    s: Seq<A>,
    prefix: Seq<B>,
    f: spec_fn(A) -> Seq<B>,
)
    requires
        s.len() > 0,
    ensures
        s.subrange(0, s.len() - 1).fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)) + f(
            s[s.len() - 1],
        ) == s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)),
{
}

} // verus!
