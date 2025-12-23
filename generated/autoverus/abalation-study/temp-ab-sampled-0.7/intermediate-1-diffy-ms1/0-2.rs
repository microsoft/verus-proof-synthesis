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
            forall |k:int| 0 <= k < i ==> a[k] == k % 1,
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum.len() == 1,
            a.len() == N,
            sum[0] == (if i == 0 { 0 } else { sum[0] }),
            forall |k:int| 0 <= k < i ==> a[k] == k % 1,
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