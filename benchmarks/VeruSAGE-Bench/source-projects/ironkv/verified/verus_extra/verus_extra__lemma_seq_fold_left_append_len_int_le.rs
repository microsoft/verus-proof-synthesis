use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_right<A>(s: Seq<A>, low: int, f: spec_fn(A) -> int)
  requires
    s.len() > 0,
  ensures
    s.subrange(0, s.len() - 1).fold_left(low, |b: int, a: A| b + f(a)) + f(s[s.len() - 1])
    ==
    s.fold_left(low, |b: int, a: A| b + f(a))
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn lemma_seq_fold_left_sum_len_int_positive<A, B>(s: Seq<A>, low: nat, f: spec_fn(A) -> Seq<B>)
  ensures
    s.fold_left(low as int, |acc: int, x: A| acc + f(x).len()) >= 0,
  decreases s.len(),
	{
		unimplemented!()
	}

pub proof fn lemma_seq_fold_left_append_len_int_le<A, B>(s: Seq<A>, i: int, low: int, f: spec_fn(A) -> Seq<B>)
  requires
    0 <= i <= s.len() as int,
    0 <= low,
  ensures
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()) >= 0,
    s.subrange(0, i).fold_left(low, |acc: int, x: A| acc + f(x).len()) <=
    s.fold_left(low, |acc: int, x: A| acc + f(x).len()),
  decreases (2 * s.len() - i),
{
  lemma_seq_fold_left_sum_len_int_positive::<A, B>(s, low as nat, f);
  let accfl = |acc: int, x: A| acc + f(x).len();
  if s.len() == 0 {
    // done
  } else if i == s.len() {
    assert_seqs_equal!(s.subrange(0, i) == s);
    lemma_seq_fold_left_append_len_int_le::<A, B>(s.subrange(1, s.len() as int), i - 1, low + f(s[0]).len() as int, f);
  } else if i == s.len() - 1 {
    let fl = |x| f(x).len() as int;
    assert(accfl =~= (|acc: int, x: A| acc + fl(x)));
    lemma_seq_fold_left_sum_right::<A>(s, low, fl);
  } else {
    lemma_seq_fold_left_append_len_int_le::<A, B>(s.subrange(0, s.len() - 1), i, low, f);
    lemma_seq_fold_left_append_len_int_le::<A, B>(s, s.len() - 1, low, f);
    assert_seqs_equal!(s.subrange(0, s.len() - 1).subrange(0, i) == s.subrange(0, i));
  }
}


}
