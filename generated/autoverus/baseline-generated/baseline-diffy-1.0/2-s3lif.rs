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
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a@[k] == 1,
            forall |k: int| i <= k < N as usize ==> a@[k] == old(a)@[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |k: int| 0 <= k < i ==> a@[k] == 4,
            forall |k: int| i <= k < N as usize ==> a@[k] == 1,
    {
        if a[i] == 1 {
            a.set(i, a[i] + 3);
        }
        i = i + 1;
    }

    i = 0;
    
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            sum@.len() == 1,
            a@.len() == N,
            sum@[0] == 4 * i as int,
            forall |k: int| 0 <= k < N as usize ==> a@[k] == 4,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// Score: (3, 2)
// Safe: False