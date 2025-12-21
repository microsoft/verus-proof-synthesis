use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::external_body]
pub proof fn lemma_seq_fold_left_merge_right_assoc<A, B>(
    s: Seq<A>,
    init: B,
    f: spec_fn(A) -> B,
    g: spec_fn(B, B) -> B,
)
    requires
        s.len() > 0,
        forall|x, y, z| #[trigger] g(g(x, y), z) == g(x, g(y, z)),
    ensures
        g(s.subrange(0, s.len() - 1).fold_left(init, |b: B, a: A| g(b, f(a))), f(s[s.len() - 1]))
            == s.fold_left(init, |b: B, a: A| g(b, f(a))),
    decreases s.len(),
{
    unimplemented!()
}

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
