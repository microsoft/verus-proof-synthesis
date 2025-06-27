
use vstd::prelude::*;

fn main() {}

verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            // The length of a is fixed during the loop
            a.len() == N as usize,
            // The first i elements of a have been set to (j % 3) for j from 0 to i-1
            a.subrange(0, i as int) == Seq::new(i, |k: int| (k % 3) as i32),
            // The remaining elements of a (from i onward) are as originally present
            a.subrange(i as int, N as int) == old(a).subrange(i as int, N as int),
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            // Ensure a hasn't changed from the first loop
            a == old(a),
            // The length of a is fixed
            a.len() == N as usize,
            // Ensure sum has been updated correctly up to index i
            sum[0] == a.subrange(0, i as int).sum(),
            // All elements of a are as originally set
            a.subrange(0, N as int) == old(a).subrange(0, N as int),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }

}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7