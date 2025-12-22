use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: seq_lib_v.rs
pub proof fn lemma_seq_fold_left_merge_right_assoc<A, B>(s: Seq<A>, init: B, f: spec_fn(A) -> B, g: spec_fn(B, B) -> B)
  requires
    s.len() > 0,
    forall |x, y, z|
      #[trigger] g(g(x, y), z) == g(x, g(y, z)),
  ensures
    g(s.subrange(0, s.len() - 1).fold_left(init, |b: B, a: A| g(b, f(a))), f(s[s.len() - 1]))
    ==
    s.fold_left(init, |b: B, a: A| g(b, f(a)))
  decreases s.len(),
{
  let emp = Seq::<B>::empty();
  let len: int = s.len() as int;
  let i = len - 1;
  let s1 = s.subrange(0, len - 1);
  let last = s[len - 1];
  let accf = |b: B, a: A| g(b, f(a));

  let start = s1.fold_left(init, accf);
  let all = s.fold_left(init, accf);

  if s1.len() == 0 {
    assert(s.len() == 1);
    reveal_with_fuel(Seq::fold_left, 2);
    reveal_with_fuel(Seq::fold_left, 2);
  } else {
    reveal_with_fuel(Seq::fold_left, 2);
    let head = s[0];
    let tail = s.subrange(1, len);
    let p = accf(init, s[0]);
    // assert(tail.len() > 0);
    // assert(all == tail.fold_left(p, accf));
    // assert(start == s1.fold_left(init, accf));
    // assert(s1.len() > 0);
    // assert(start == s1.subrange(1, s1.len() as int).fold_left(p, accf));
    // assert(start == s1.subrange(1, len - 1).fold_left(p, accf));
    assert_seqs_equal!(tail.subrange(0, len - 2) == s1.subrange(1, len - 1));
    // assert(start == tail.subrange(0, tail.len() - 1).fold_left(p, accf));
    // assert(all == tail.fold_left(p, accf));
    lemma_seq_fold_left_merge_right_assoc::<A, B>(tail, p, f, g);
    // assert(all == g(start, f(last)));
  }
}


}
