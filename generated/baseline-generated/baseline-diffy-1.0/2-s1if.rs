use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] == N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N ==> old(a)[k] == a[k],
            sum[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
            sum[0] == i,
    {
        if (a[i] == 1) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (3, 0)
// Safe: True