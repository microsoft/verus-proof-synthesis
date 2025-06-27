use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    // First loop
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
            forall |k:int| k >= i && k < N ==> a[k] == old(a)[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    // Second loop
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            b@.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 1,
            forall |k:int| k >= i && k < N ==> b[k] == old(b)[k],
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    // Third loop
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            a@.len() == N,
            forall |k:int| 0 <= k < a.len() ==> a[k] == 1,
            sum[0] == i,  // sum accumulates count of 1's up to i
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    
    // Fourth loop
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            b@.len() == N,
            sum@.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == N + 1,
            forall |k:int| k >= i && k < N ==> a[k] == 1,
            sum[0] == N,
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}
}
// Score: (4, 2)
// Safe: True