

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
            0 < N < 100,
            // Invariants specific to the first loop: values set in 'a' up to i
            forall |j: usize| j < i ==> a[( j ) as int] == j % 2,
    {
        a.set(i, i % 2);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            0 < N < 100,
            // Invariants for the second loop: sum is accumulated correctly and does not exceed N
            sum[0] <= N,
            forall |j: usize| j < i ==> a[( j ) as int] == j % 2,
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5