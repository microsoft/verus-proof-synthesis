use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while i < N
    invariant
        0 <= i <= N,
        a.len() == N,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    {
        a.set(i, 1);
        i += 1;
    }

    i = 0;

    while i < N
    invariant
        0 <= i <= N,
        a.len() == N,
        forall |k: int| 0 <= k < i ==> a[k] == 2,
        forall |k: int| i <= k < N ==> a[k] == 1,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    {
        if a[i] == 1 {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i += 1;
    }

    i = 0;

    while i < N
    invariant
        0 <= i <= N,
        sum.len() == 1,
        sum[0] == 2 * i, // Added to track sum progression
        a.len() == N,
        forall |k: int| 0 <= k < N ==> a[k] == 2,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    {
        if a[i] == 2 {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i += 1;
    }
}
}
// Score: (4, 0)
// Safe: False