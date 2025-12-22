use vstd::prelude::*;

fn main() {}
verus! {

/// Equivalent to `choose |i:int| low <= i < high && p(i)` except it guarantees to pick the smallest
/// such value `i` where `p(i)` is true.
pub proof fn choose_smallest(low: int, high: int, p: spec_fn(int)->bool) -> (res:int)
  requires
    exists |i:int| #![trigger(p(i))] low <= i < high && p(i),
  ensures
    low <= res < high,
    p(res),
    forall |i:int| #![trigger(p(i))] low <= i < res ==> !p(i),
  decreases
    high - low,
{
  if p(low) {
    low
  } else {
    choose_smallest(low + 1, high, p)
  }
}

} // verus!
