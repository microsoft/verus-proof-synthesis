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
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N as int,
            forall |j: int| 0 <= j < i as int ==> a[j] == 4,
            forall |j: int| i as int <= j < N as int ==> a[j] == old(a)[j],
    {
        a.set(i, 4);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            a@.len() == N as int,
            forall |j: int| 0 <= j < N as int ==> a[j] == 4,
            sum[0] == 4 * i as int,
    {
        if a[i] == 4 {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (2, 2)
// Safe: False