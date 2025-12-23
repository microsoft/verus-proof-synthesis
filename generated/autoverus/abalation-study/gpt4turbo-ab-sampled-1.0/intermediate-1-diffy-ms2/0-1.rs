
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

    while (i < N as usize)
        invariant 
            i <= N,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == k % 2,
    {
        a.set(i, i % 2 );
        i = i + 1;
    }

    i = 0;

    sum.set(0, 0);
    
    while (i < N as usize)
        invariant 
            i <= N,
            sum.len() == 1,
            sum[0] <= i, // the maximum sum[0] can be the number of odd numbers <= i, which is at most i
            a.len() == N,
    {
        if (i != 0) {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2