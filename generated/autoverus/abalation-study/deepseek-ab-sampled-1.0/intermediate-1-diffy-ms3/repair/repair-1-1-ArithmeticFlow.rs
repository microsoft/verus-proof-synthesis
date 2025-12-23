
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            sum.len() == 1,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            i <= N as usize,
            N as usize > 0,
            N < 1000,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> sum[0] == (sum[0] + a[k]),
            i <= N as usize,
            N as usize > 0,
            N < 1000,
            sum[0] <= 2 * N, // Added: upper bound for sum[0]
            sum[0] <= 2 * i, // Added: upper bound based on loop index
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


//             sum.set(0, sum[0] + a[i]);
//   None: sum[0] + a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False