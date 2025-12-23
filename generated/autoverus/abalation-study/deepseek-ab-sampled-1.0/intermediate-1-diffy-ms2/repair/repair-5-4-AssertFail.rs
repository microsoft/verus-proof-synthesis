

use vstd::prelude::*;
fn main() {}
verus! {

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
    let ghost sum_i = 0;
    proof {
        let ghost sum_i = sum.len();
        assert(sum[0] <= 0); // When i==0, sum[0] is 0
        if (sum[0] == 0) {
            // Add condition to ensure sum[0] is within expected bounds
            assert(sum[0] <= 0);
        }
    }
    let mut i_sum = 0;
    while (i_sum < N as usize)
        invariant
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == k % 2,
            i_sum <= N,
            sum.len() == 1,
            sum[0] <= i_sum,
    {
        if (i_sum == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i_sum]);
        }
        i_sum = i_sum + 1;
    }
}
}

//         assert(sum[0] <= 0); // When i==0, sum[0] is 0
//   assertion failed: sum[0] <= 0

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False