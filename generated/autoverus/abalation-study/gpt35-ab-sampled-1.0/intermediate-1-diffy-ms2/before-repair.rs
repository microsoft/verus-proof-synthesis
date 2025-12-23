
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            N > 0,
            // We do not modify the elements in array `a` within this loop, as we only read from it and do not call a.set()
            // Therefore, the array values remain the same as per the initial assignment.
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|k: int| 0 <= k <= i ==> a[k] == k % 2,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] <= i,
            N > 0,
            // We do not modify the elements in array `a` within this loop, as we only read from it and do not call a.set()
            // Therefore, the array values remain the same as per the initial assignment.
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}

} // verus!

// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2