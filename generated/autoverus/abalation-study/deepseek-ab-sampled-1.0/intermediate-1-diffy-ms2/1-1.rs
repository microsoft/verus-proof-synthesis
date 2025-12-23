

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;

    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            sum.len() ==1,
            N >0,
            0 <= sum[0] <= N,
            // At each step up to i, a[k] == k % 2 for all k < i
            forall |k: usize| k < i ==> a[( k ) as int] == k % 2,
    {
        a.set(i, i % 2);
        i = i + 1;
    }

    // Reset variables for second loop
    i = 0;
    sum.set(0, 0);

    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            sum.len() ==1,
            N >0,
            // sum[0] is the sum of a[0] to a[i-1]
            sum[0] == a[( 0..i ) as int].iter().sum(),
            // Since a[k] %2 is either 0 or 1, sum[0] <= i
            sum[0] <= N,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2