use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
pub proof fn lemma_fold_left_append_merge<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> Seq<B>)
  ensures
    (s1 + s2).fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      ==
    s1.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
      +
    s2.fold_left(Seq::empty(), |acc: Seq<B>, a: A| acc + f(a))
  decreases
    s1.len() + s2.len()
{
  let e = Seq::<B>::empty();
  let af = |acc: Seq<B>, a: A| acc + f(a);
  let fl = |s: Seq<A>| s.fold_left(e, af);
  if s2.len() == 0 {
    assert(s1 + s2 =~= s1);
    assert(fl(s1) =~= fl(s1) + e);
  } else {
    lemma_fold_left_append_merge(s1, s2.drop_last(), f);
    assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
    assert((fl(s1) + fl(s2.drop_last())) + f(s2.last()) =~= fl(s1) + (fl(s2.drop_last()) + f(s2.last())));
  }
}


}
