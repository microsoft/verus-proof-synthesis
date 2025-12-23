

rust
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
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            (old(sum).len() == 1),
            (forall |j: int| 0 <= j < i ==> a[j] == 1),
            sum[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            (old(sum).len() == 1),
            (forall |j: int| 0 <= j < N ==> a[j] == 1),
            (forall |j: int| 0 <= j < i ==> b[j] == 1),
            (sum[0] == 0),
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            (old(sum).len() == 1),
            (forall |j: int| 0 <= j < N ==> a[j] == 1),
            (forall |j: int| 0 <= j < N ==> b[j] == 1),
            (sum[0] == 2*N - i),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            (old(sum).len() == 1),
            (forall |j: int| 0 <= j < N ==> a[j] == 1),

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1