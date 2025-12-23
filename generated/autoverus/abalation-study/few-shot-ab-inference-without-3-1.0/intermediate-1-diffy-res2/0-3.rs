use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            forall |k:int| 0 <= k < i as int ==> a[k] == 1
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            forall |k:int| 0 <= k < a.len() as int ==> a[k] == 1,
            sum[0] <= i as i32,
            forall |k:int| 0 <= k < i as int ==> sum[0] == k as i32 + 1
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            b.len() == N,
            forall |k:int| 0 <= k < i as int ==> b[k] == 1
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            b.len() == N,
            forall |k:int| 0 <= k < b.len() as int ==> b[k] == 1,
            sum[0] <= i as i32 + N,
            forall |k:int| 0 <= k < i as int ==> sum[0] == k as i32 + N + 1
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            c.len() == N,
            forall |k:int| 0 <= k < i as int ==> c[k] == 1
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            c.len() == N,
            forall |k:int| 0 <= k < c.len() as int ==> c[k] == 1,
            sum[0] <= i as i32 + 2 * N,
            forall |k:int| 0 <= k < i as int ==> sum[0] == k as i32 + 2 * N + 1
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1