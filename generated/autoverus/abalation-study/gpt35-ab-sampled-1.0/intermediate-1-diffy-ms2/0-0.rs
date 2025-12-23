
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
            old(a).len() == N,
            old(sum).len() == 1,
    {
        a.set(i, i % 2 );
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            sum.len() == 1,
            N > 0,
            old(a).len() == N,
            old(sum).len() == 1,
            (i == 0 && sum[0] == 0) || (i > 0 && sum[0] == i / 2), // loop invariant
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