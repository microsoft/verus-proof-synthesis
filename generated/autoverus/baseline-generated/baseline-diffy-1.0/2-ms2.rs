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

    while i < N as usize
    invariant
        0 <= i <= N,
        a@.len() == N,
        forall |k: int| 0 <= k < i ==> a[k] == k % 2,
        forall |k: int| i <= k < N ==> a[k] == old(a)[k],
    {
        a.set(i, i % 2 );
        i = i + 1;
    }

    i = 0;

    while i < N as usize
    invariant
        0 <= i <= N,
        sum@.len() == 1,
        a@.len() == N,
        forall |k: int| 0 <= k < a@.len() ==> a[k] == k % 2,
        sum[0] <= i,
        sum[0] <= i/2,
        sum[0] <= 1 + i/2,  
    {
        if i == 0 {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        assert(sum[0] <= (i + 1)/2);
        i = i + 1;
    }
}

}
// Score: (2, 2)
// Safe: False