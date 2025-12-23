
use vstd::prelude::*;

#[verifier::loop_isolation(false)]

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
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    sum.set(0, 0);
    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == k % 2,
            sum.len() == 1,
            // sum[0] is the sum of the first i elements of a
            sum[0] == seq![for j: usize in 0..i => a[j]].sum(),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}


//             sum[0] == i,
//   None: sum[0] == i

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False