use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    // First loop: Initialize all elements of `a` to `1`
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    // Second loop: Update all elements of `a` based on their initial values
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 2,
            forall |k: int| i <= k < N as int ==> a[k] == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    
    // Third loop: Accumulate the sum of all elements in `a`
    while (i < N as usize) 
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            sum[0] == i as i32,
            forall |k: int| 0 <= k < N as int ==> a[k] == 2,
            sum[0] == 2 * i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    assert(sum[0] == 2 * N);
}
}
// Score: (3, 1)
// Safe: True