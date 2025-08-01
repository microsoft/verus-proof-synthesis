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
        sum[0] == 6 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    
    while i < N as usize
        invariant
            i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < (i as int) ==> a@[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < (i as int) ==> a@[k] == 6,
            forall |k: int| (i as int) <= k < N ==> a@[k] == 1,
    {
        if a[i] == 1 {
            a.set(i, a[i] + 5);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            i <= N as usize,
            sum@.len() == 1,
            a@.len() == N,
            forall |k: int| 0 <= k < N ==> a@[k] == 6,
            sum@[0] == (i as int) * 6,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// Score: (3, 2)
// Safe: False