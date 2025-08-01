

use vstd::prelude::*;
fn main() {}

verus!{

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
            i <= N,
            a.len() == N,
            N < 1000,
            sum.len() == 1,
            // Assertion for the loop that all elements of a are set to 0, 1, or 2.
            forall |k:int| 0<= k < i ==> a[k] == (k % 3) as i32,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant 
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            // Calculation ensures the sum doesn't exceed 2*N.
            a[( i ) as int] <= 2,
            sum[0] <= 2 * (N - (i as i32)),
        {
            if (i == 0) {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
        }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4