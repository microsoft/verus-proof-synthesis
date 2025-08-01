

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
            i <= N,
            N < 1000,
            a.len() == N,
            ∀ |j: int| (0 <= j < i) ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] <= N,
            a.len() == N,
            ∀ |j: int| (0 <= j < i) ==> a[j] == 1,
            ∀ |j: int| (0 <= j < b.len()) ==> b[j] == old(b)[j],
            ∀ |j: int| (0 <= j < c.len()) ==> c[j] == old(c)[j],
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            b.len() == N,
            ∀ |j: int| (0 <= j < i) ==> b[j] == 1,
            ∀ |j: int| (0 <= j < a.len()) ==> a[j] == old(a)[j],
            ∀ |j: int| (0 <= j < c.len()) ==> c[j] == old(c)[j],
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] <= 2 * N,
            b.len() == N,
            ∀ |j: int| (0 <= j < i) ==> b[j] == 1,
            ∀ |j: int| (0 <= j < a.len()) ==> a[j] == old(a)[j],
            ∀ |j: int| (0 <= j < c.len()) ==> c[j] == old(c)[j],
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            c.len() == N,
            ∀ |j: int| (0 <= j < i) ==> c[j] == 1,
            ∀ |j: int| (0 <= j < a.len()) ==> a[j] == old(a)[j],
            ∀ |j: int| (0 <= j < b.len()) ==> b[j] == old(b)[j],
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] <= 3 * N,
            c.len() == N,
            ∀ |j: int| (0 <= j < i) ==> c[j] == 1,
            ∀ |j: int| (0 <= j < a.len()) ==> a[j] == old(a)[j],
            ∀ |j: int| (0 <= j < b.len()) ==> b[j] == old(b)[j],
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 16