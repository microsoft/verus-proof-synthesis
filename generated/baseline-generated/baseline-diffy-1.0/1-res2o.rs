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
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N as int,
            forall |k: int| 0 <= k < i as int ==> a[k] == 1
    {
        a.set(i, 1);
        i += 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            b@.len() == N as int,
            forall |k: int| 0 <= k < i as int ==> b[k] == 1
    {
        b.set(i, 1);
        i += 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            c@.len() == N as int,
            forall |k: int| 0 <= k < i as int ==> c[k] == 1
    {
        c.set(i, 1);
        i += 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            sum[0] <= i as i32,
            a@.len() == N as int,
            forall |k: int| 0 <= k < N as int ==> a[k] == 1
    {
        sum.set(0, sum[0] + a[i]);
        i += 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            sum[0] <= N + i as i32,
            b@.len() == N as int,
            forall |k: int| 0 <= k < N as int ==> b[k] == 1
    {
        sum.set(0, sum[0] + b[i]);
        i += 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            sum[0] <= 2 * N + i as i32,
            c@.len() == N as int,
            forall |k: int| 0 <= k < N as int ==> c[k] == 1
    {
        sum.set(0, sum[0] + c[i]);
        i += 1;
    }
}
}
// Score: (5, 2)
// Safe: False