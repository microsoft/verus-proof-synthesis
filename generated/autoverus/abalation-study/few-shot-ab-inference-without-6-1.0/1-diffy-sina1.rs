use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            i <= N,
            N > 0,
            a.len() == N,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            N > 0,
            a.len() == N,
            sum.len() == 1,
            sum[0] == N,
            forall |k:int| 0 <= k < i ==> a[k] == N,
    {
        a.set(i, sum[0]);
        i = i + 1;
    }
}
}
// Score: (3, 0)
// Safe: True