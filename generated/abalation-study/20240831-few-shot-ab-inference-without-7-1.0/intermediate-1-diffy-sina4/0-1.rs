use vstd::prelude::*;
fn main() {}
verus! {
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k: int| 0 <= k < N ==> b[k] == N + 2,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            forall |j: int| 0 <= j < i ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            forall |j: int| 0 <= j < i ==> sum[0] == j,
            forall |j: int| 0 <= j < i ==> a[j] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            forall |j: int| 0 <= j < i ==> a[j] == 1 + sum[0],
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i ==> b[j] == a[j] + 1,
            forall |j: int| 0 <= j < N ==> a[j] == 1 + sum[0],
            sum[0] == N,
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1