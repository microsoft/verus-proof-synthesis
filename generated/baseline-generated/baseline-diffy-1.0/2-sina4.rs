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
        forall |k:int| 0 <= k < N ==> b[k] == N + 2,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    // First loop
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N ==> old(a)[k] == a[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Second loop
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] >= 0, // sum in the loop is always non-negative
            sum[0] == i as i32,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N ==> a[k] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;

    // Third loop
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == N,
            forall |k: int| 0 <= k < i ==> a[k] == N + 1,
            forall |k: int| i <= k < N ==> a[k] == 1,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;

    // Fourth loop
    while (i < N as usize)
        invariant
            0 <= i <= N,
            b.len() == N,
            a.len() == N,
            forall |k: int| 0 <= k < i ==> b[k] == N + 2,
            forall |k: int| i <= k < N ==> a[k] == N + 1,
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}
// Score: (3, 4)
// Safe: True