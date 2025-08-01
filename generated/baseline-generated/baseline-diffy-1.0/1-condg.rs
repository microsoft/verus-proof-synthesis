use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == 0,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            forall |k: int| 0 <= k < i as int ==> a[k] == 1,
            forall |k: int| i as int <= k < N ==> a[k] == old(a)[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() > 0,
            sum[0] == i as i32,
            a.len() == N,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() > 0,
            sum[0] == N,
            a.len() == N,
            forall |k: int| 0 <= k < i as int ==> a[k] == 0,
            forall |k: int| i as int <= k < N ==> a[k] == 1,
    {
        if sum[0] == N {
            a.set(i, a[i] - 1);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
}
}
// Score: (4, 0)
// Safe: False