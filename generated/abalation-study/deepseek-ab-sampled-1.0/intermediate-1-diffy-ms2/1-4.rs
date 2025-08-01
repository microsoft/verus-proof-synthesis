
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
            sum.len() == 1,
            // Each a[i] has been set correctly based on i % 2
            forall |j: usize| j < i ==> a[( j ) as int] == j % 2,
    {
        a.set(i, i % 2 );
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant 
            i <= N,
            a.len() == N,
            sum.len() == 1,
            // sum[0] is the sum of a[0..i)
            sum[0] == (i..N as usize).map(|j| a[j]).sum(),
            sum[0] <= i,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2