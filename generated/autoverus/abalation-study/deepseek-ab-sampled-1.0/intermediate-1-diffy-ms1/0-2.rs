

use vstd::prelude::*;
fn main() {}

verus!{

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant 
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |k: usize| k < i ==> a[k] == k % 1, // Tracking a's initial state
    {
        a.set(i, i % 1);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant 
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |k: usize| k < i ==> (if k == 0 then sum[0] == 0 else sum[0] == sum[0] + a[k]),
    // Description: Ensuring the sum is correctly calculated up to index i
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
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1