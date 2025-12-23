use vstd::prelude::*;
fn main() {}
verus! {
fn myfun( ) -> (r: i32)
{
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    while i < 100
        invariant
          i <= 100,
          i >= 0,
          i * i <= 100 * i, // Added by AI, using 100 * i as the upper bound
    {
      sum = i * i;
    }
    sum
}
}
