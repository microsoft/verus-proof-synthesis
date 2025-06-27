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
        sum[0] <= 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
            forall |k:int| i <= k < N ==> a[k] == old(a)[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
            sum[0] <= 2 * N, // to support function post-condition
            sum[0] >= i as i32, // partial sum invariant
            old(sum)[0] == 0,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            b.len() == N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            forall |k:int| 0 <= k < i ==> b[k] == 1,
            forall |k:int| i <= k < N ==> b[k] == old(b)[k],
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            b.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
            sum[0] <= 2 * N, // to support function post-condition
            sum[0] >= (N + i as i32), // partial sum invariant
            old(sum)[0] == 0,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 3