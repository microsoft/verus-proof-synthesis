
use vstd::prelude::*;

fn main() {}

#[verifier::loop_isolation(false)]

verus! {
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
    proof {
        assert(sum[0] + a[i as int] <= 2 * N);
        assert(sum[0] >= 0);
    }
    while (i < N as usize)
        invariant
            a.len() == N,
            sum.len() == 1,
            sum[0] + a[(i) as int] <= 2 * N,
            a[(i) as int] >= 0,
            a[(i) as int] <= 2,
            sum[0] >= 0,
            sum[0] <= 2 * i as i32, // Added upper bound based on loop index
            i <= N as usize,
            N as usize > 0,
            N < 1000,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
        assert(sum[0] <= 2 * N);
    }
}
}


//             sum[0] >= 0,
//   None: sum[0] >= 0

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 6
// Safe: True