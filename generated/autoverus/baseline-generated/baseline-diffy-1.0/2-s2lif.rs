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
        sum[0] == 3 * N,
{
    sum.set(0, 0);

    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N as int ==> old(a)[k] == a[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 3,
            forall |k: int| i <= k < N as int ==> a[k] == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            a@.len() == N,
            sum[0] == 3 * i,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// Score: (3, 2)
// Safe: True