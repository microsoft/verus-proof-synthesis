use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N as int, // keep the length of a unchanged
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N as int ==> a[k] == old(a)@[k],
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a@.len() == N as int, // keep the length of a unchanged
            sum@.len() == 1, // keep the length of sum unchanged
            sum[0] <= i as int, // ensure sum[0] is within the size of N during loop iterations
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N as int ==> a[k] == 1 || a[k] == 0,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (1, 2)
// Safe: True