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
            i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == i * 1, // Since a[j] == 1 for all j in [0, i), sum[0] should be i
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N * 1, // Since a[j] == 1 for all j in [0, N), sum[0] should be N
            forall |j: int| 0 <= j < i ==> a[j] == N + 1,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N,
            forall |j: int| 0 <= j < N ==> a[j] == N + 1,
            forall |j: int| 0 <= j < i ==> b[j] == N + 2,
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 3, Verus Errors: 6