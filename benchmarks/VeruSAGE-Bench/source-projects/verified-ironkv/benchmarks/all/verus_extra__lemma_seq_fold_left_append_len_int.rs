use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
pub proof fn lemma_seq_fold_left_append_len_int<A, B>(s: Seq<A>, prefix: Seq<B>, f: spec_fn(A) -> Seq<B>)
  ensures
    s.fold_left(prefix, |sb: Seq<B>, a: A| sb + f(a)).len() as int
    ==
    s.fold_left(prefix.len() as int, |i: int, a: A| i + f(a).len() as int),
  decreases s.len(),
{
  s.lemma_fold_left_alt(prefix, |sb: Seq<B>, a: A| sb + f(a));
  s.lemma_fold_left_alt(prefix.len() as int, |i: int, a: A| i + f(a).len() as int);
  if s.len() != 0 {
    lemma_seq_fold_left_append_len_int::<A, B>(s.subrange(1, s.len() as int), prefix + f(s[0]), f);
    s.subrange(1, s.len() as int).lemma_fold_left_alt(prefix + f(s[0]), |sb: Seq<B>, a: A| sb + f(a));
    s.subrange(1, s.len() as int).lemma_fold_left_alt(prefix.len() as int + f(s[0]).len() as int, |i: int, a: A| i + f(a).len() as int);
  }
}


}
