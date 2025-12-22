use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_fold_left_append_merge<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> Seq<B>)
    ensures
        (s1 + s2).fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a)) == s1.fold_left(
            Seq::empty(),
            |acc: Seq<B>, a: A| acc + f(a),
        ) + s2.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a)),
{
}

} // verus!
