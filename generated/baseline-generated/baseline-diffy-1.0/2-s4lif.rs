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
        sum[0] == 5 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i as int ==>
                a@.index(k) == 1,
            sum@.len() == 1,
            sum@[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i as int ==>
                a@.index(k) == 5,
            forall |k: int| i as int <= k < N ==>
                a@.index(k) == 1,
            sum@.len() == 1,
            sum@[0] == 0,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 4);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            sum@[0] == 5 * i as int,
            forall |k: int| 0 <= k < N ==>
                a@[k] == 5,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// Score: (3, 2)
// Safe: True