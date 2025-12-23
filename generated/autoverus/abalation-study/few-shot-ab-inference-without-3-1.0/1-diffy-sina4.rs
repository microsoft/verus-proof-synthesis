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
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N < 1000,
            i <= N as usize,
            forall |k:int| 0 <= k < i as int ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < a.len() ==> a[k] == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N,
            forall |k:int| 0 <= k < i as int ==> a[k] == N + 1,
            forall |k:int| i <= k < a.len() ==> a[k] == 1,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N,
            forall |k:int| 0 <= k < a.len() ==> a[k] == N + 1,
            forall |k:int| 0 <= k < i as int ==> b[k] == N + 2,
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}
// Score: (5, 0)
// Safe: True