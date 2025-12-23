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

    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            forall |j: int| 0 <= j < i as int ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            forall |j: int| 0 <= j < i as int ==> b[j] == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] <= i as i32,
            forall |j: int| 0 <= j < N as int ==> a[j] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            sum.len() == 1,
            sum[0] <= (N + i as i32),
            forall |j: int| 0 <= j < N as int ==> b[j] == 1,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
}
}
// Score: (4, 1)
// Safe: False