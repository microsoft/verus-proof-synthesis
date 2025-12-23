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
    {
      sum = i * i;
    }
    sum
}
}
